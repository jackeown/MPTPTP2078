%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t31_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   43 (  65 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 319 expanded)
%              Number of equality atoms :   36 (  66 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2597,plain,(
    $false ),
    inference(resolution,[],[f2596,f105])).

fof(f105,plain,(
    r2_hidden(sK2(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,sK0)) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f39])).

fof(f39,plain,
    ( ? [X0] : ~ r1_setfam_1(k4_setfam_1(X0,X0),X0)
   => ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] : ~ r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t31_setfam_1.p',t31_setfam_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK2(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK3(X1,X4))
              & r2_hidden(sK3(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK3(X1,X4))
        & r2_hidden(sK3(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t31_setfam_1.p',d2_setfam_1)).

fof(f2596,plain,(
    ! [X0] : ~ r2_hidden(sK2(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,X0)) ),
    inference(duplicate_literal_removal,[],[f2595])).

fof(f2595,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,X0))
      | ~ r2_hidden(sK2(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,X0)) ) ),
    inference(resolution,[],[f1945,f94])).

fof(f94,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k4_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k6_subset_1(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( k6_subset_1(sK5(X0,X1,X2),sK6(X0,X1,X2)) = sK4(X0,X1,X2)
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k6_subset_1(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k6_subset_1(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X1)
                & r2_hidden(sK7(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f50,f53,f52,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k6_subset_1(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k6_subset_1(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k6_subset_1(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k6_subset_1(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k6_subset_1(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k6_subset_1(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k6_subset_1(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k6_subset_1(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k6_subset_1(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k6_subset_1(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k6_subset_1(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k6_subset_1(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k6_subset_1(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k6_subset_1(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t31_setfam_1.p',d6_setfam_1)).

fof(f1945,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK7(X1,X2,sK2(k4_setfam_1(sK0,sK0),sK0)),sK0)
      | ~ r2_hidden(sK2(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(X1,X2)) ) ),
    inference(resolution,[],[f1788,f731])).

fof(f731,plain,(
    ! [X6,X7,X5] :
      ( m1_subset_1(X7,k1_zfmisc_1(sK7(X5,X6,X7)))
      | ~ r2_hidden(X7,k4_setfam_1(X5,X6)) ) ),
    inference(superposition,[],[f85,f92])).

fof(f92,plain,(
    ! [X0,X8,X1] :
      ( k4_xboole_0(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k4_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_xboole_0(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f78,f63])).

fof(f63,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t31_setfam_1.p',redefinition_k6_subset_1)).

fof(f78,plain,(
    ! [X2,X0,X8,X1] :
      ( k6_subset_1(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f62,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t31_setfam_1.p',dt_k6_subset_1)).

fof(f1788,plain,(
    ! [X8] :
      ( ~ m1_subset_1(sK2(k4_setfam_1(sK0,sK0),sK0),k1_zfmisc_1(X8))
      | ~ r2_hidden(X8,sK0) ) ),
    inference(resolution,[],[f332,f55])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(sK2(X0,X1),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f70,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t31_setfam_1.p',t3_subset)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
