%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:55 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 946 expanded)
%              Number of leaves         :   14 ( 288 expanded)
%              Depth                    :   28
%              Number of atoms          :  301 (5909 expanded)
%              Number of equality atoms :  111 (2678 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1478,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1469,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1469,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f1436,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1436,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(resolution,[],[f1079,f1245])).

fof(f1245,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(backward_demodulation,[],[f1086,f1209])).

fof(f1209,plain,(
    sK0 = sK6(k1_xboole_0) ),
    inference(resolution,[],[f1076,f1080])).

fof(f1080,plain,(
    r2_hidden(sK6(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f1075,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f41])).

fof(f41,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f1075,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f106,f1033])).

fof(f1033,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f1032,f1019])).

fof(f1019,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f1016,f55])).

fof(f55,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).

fof(f24,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f1016,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(duplicate_literal_removal,[],[f1015])).

fof(f1015,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f64,f1010])).

fof(f1010,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f1009,f982])).

fof(f982,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0) ),
    inference(resolution,[],[f534,f107])).

fof(f107,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f534,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK2(k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK1(k1_tarski(sK0),X2),X2)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f55,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK1(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f1009,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f1008,f106])).

fof(f1008,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f1007,f55])).

fof(f1007,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f997])).

fof(f997,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f982,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1032,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f1031,f106])).

fof(f1031,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f1030,f55])).

fof(f1030,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f1020])).

fof(f1020,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f1019,f62])).

fof(f106,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1076,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | sK0 = X6 ) ),
    inference(superposition,[],[f107,f1033])).

fof(f1086,plain,(
    ~ r2_hidden(sK0,sK6(k1_xboole_0)) ),
    inference(resolution,[],[f1075,f119])).

fof(f119,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1079,plain,(
    ! [X1] :
      ( r2_hidden(sK0,X1)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f1075,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (20086)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (20071)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (20087)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (20065)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (20072)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (20078)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (20066)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (20073)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (20079)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (20093)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (20080)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (20066)Refutation not found, incomplete strategy% (20066)------------------------------
% 0.22/0.52  % (20066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20066)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20066)Memory used [KB]: 10746
% 0.22/0.52  % (20066)Time elapsed: 0.080 s
% 0.22/0.52  % (20066)------------------------------
% 0.22/0.52  % (20066)------------------------------
% 0.22/0.52  % (20082)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (20085)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (20084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (20085)Refutation not found, incomplete strategy% (20085)------------------------------
% 0.22/0.52  % (20085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20085)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20085)Memory used [KB]: 1791
% 0.22/0.52  % (20085)Time elapsed: 0.127 s
% 0.22/0.52  % (20085)------------------------------
% 0.22/0.52  % (20085)------------------------------
% 0.22/0.52  % (20083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (20084)Refutation not found, incomplete strategy% (20084)------------------------------
% 0.22/0.52  % (20084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20064)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (20081)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (20090)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (20088)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (20077)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (20069)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (20072)Refutation not found, incomplete strategy% (20072)------------------------------
% 0.22/0.53  % (20072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20067)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (20091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (20089)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (20092)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (20068)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (20072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20072)Memory used [KB]: 10746
% 0.22/0.53  % (20072)Time elapsed: 0.116 s
% 0.22/0.53  % (20072)------------------------------
% 0.22/0.53  % (20072)------------------------------
% 0.22/0.53  % (20070)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20074)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (20074)Refutation not found, incomplete strategy% (20074)------------------------------
% 0.22/0.54  % (20074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20074)Memory used [KB]: 10618
% 0.22/0.54  % (20074)Time elapsed: 0.131 s
% 0.22/0.54  % (20074)------------------------------
% 0.22/0.54  % (20074)------------------------------
% 0.22/0.54  % (20084)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20084)Memory used [KB]: 10746
% 0.22/0.54  % (20084)Time elapsed: 0.124 s
% 0.22/0.54  % (20084)------------------------------
% 0.22/0.54  % (20084)------------------------------
% 0.22/0.54  % (20081)Refutation not found, incomplete strategy% (20081)------------------------------
% 0.22/0.54  % (20081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20081)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20081)Memory used [KB]: 10618
% 0.22/0.54  % (20081)Time elapsed: 0.123 s
% 0.22/0.54  % (20081)------------------------------
% 0.22/0.54  % (20081)------------------------------
% 0.22/0.54  % (20076)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20075)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.05/0.65  % (20104)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.05/0.66  % (20106)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.05/0.68  % (20112)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.05/0.68  % (20117)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.05/0.68  % (20121)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.05/0.68  % (20115)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.59/0.76  % (20087)Refutation found. Thanks to Tanya!
% 2.59/0.76  % SZS status Theorem for theBenchmark
% 2.59/0.77  % SZS output start Proof for theBenchmark
% 2.59/0.77  fof(f1478,plain,(
% 2.59/0.77    $false),
% 2.59/0.77    inference(subsumption_resolution,[],[f1469,f56])).
% 2.59/0.77  fof(f56,plain,(
% 2.59/0.77    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.59/0.77    inference(cnf_transformation,[],[f11])).
% 2.59/0.77  fof(f11,axiom,(
% 2.59/0.77    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.59/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.59/0.77  fof(f1469,plain,(
% 2.59/0.77    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 2.59/0.77    inference(resolution,[],[f1436,f74])).
% 2.59/0.77  fof(f74,plain,(
% 2.59/0.77    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/0.77    inference(cnf_transformation,[],[f40])).
% 2.59/0.77  fof(f40,plain,(
% 2.59/0.77    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/0.77    inference(nnf_transformation,[],[f13])).
% 2.59/0.77  fof(f13,axiom,(
% 2.59/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.59/0.77  fof(f1436,plain,(
% 2.59/0.77    ~r1_tarski(k1_xboole_0,sK0)),
% 2.59/0.77    inference(resolution,[],[f1079,f1245])).
% 2.59/0.77  fof(f1245,plain,(
% 2.59/0.77    ~r2_hidden(sK0,sK0)),
% 2.59/0.77    inference(backward_demodulation,[],[f1086,f1209])).
% 2.59/0.77  fof(f1209,plain,(
% 2.59/0.77    sK0 = sK6(k1_xboole_0)),
% 2.59/0.77    inference(resolution,[],[f1076,f1080])).
% 2.59/0.77  fof(f1080,plain,(
% 2.59/0.77    r2_hidden(sK6(k1_xboole_0),k1_xboole_0)),
% 2.59/0.77    inference(resolution,[],[f1075,f76])).
% 2.59/0.77  fof(f76,plain,(
% 2.59/0.77    ( ! [X0,X1] : (r2_hidden(sK6(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.59/0.77    inference(cnf_transformation,[],[f42])).
% 2.59/0.77  fof(f42,plain,(
% 2.59/0.77    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.59/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f41])).
% 2.59/0.77  fof(f41,plain,(
% 2.59/0.77    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)))),
% 2.59/0.77    introduced(choice_axiom,[])).
% 2.59/0.77  fof(f20,plain,(
% 2.59/0.77    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.59/0.77    inference(ennf_transformation,[],[f10])).
% 2.59/0.77  fof(f10,axiom,(
% 2.59/0.77    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.59/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 2.59/0.77  fof(f1075,plain,(
% 2.59/0.77    r2_hidden(sK0,k1_xboole_0)),
% 2.59/0.77    inference(superposition,[],[f106,f1033])).
% 2.59/0.77  fof(f1033,plain,(
% 2.59/0.77    k1_xboole_0 = k1_tarski(sK0)),
% 2.59/0.77    inference(subsumption_resolution,[],[f1032,f1019])).
% 2.59/0.77  fof(f1019,plain,(
% 2.59/0.77    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.59/0.77    inference(subsumption_resolution,[],[f1016,f55])).
% 2.59/0.77  fof(f55,plain,(
% 2.59/0.77    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.59/0.77    inference(cnf_transformation,[],[f25])).
% 2.59/0.77  fof(f25,plain,(
% 2.59/0.77    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.59/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).
% 2.59/0.77  fof(f24,plain,(
% 2.59/0.77    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.59/0.77    introduced(choice_axiom,[])).
% 2.59/0.77  fof(f17,plain,(
% 2.59/0.77    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.59/0.77    inference(ennf_transformation,[],[f16])).
% 2.59/0.77  fof(f16,negated_conjecture,(
% 2.59/0.77    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.59/0.77    inference(negated_conjecture,[],[f15])).
% 2.59/0.77  fof(f15,conjecture,(
% 2.59/0.77    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.59/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.59/0.77  fof(f1016,plain,(
% 2.59/0.77    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 2.59/0.77    inference(duplicate_literal_removal,[],[f1015])).
% 2.59/0.77  fof(f1015,plain,(
% 2.59/0.77    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.59/0.77    inference(superposition,[],[f64,f1010])).
% 2.59/0.77  fof(f1010,plain,(
% 2.59/0.77    sK0 = sK2(k1_tarski(sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.59/0.77    inference(subsumption_resolution,[],[f1009,f982])).
% 2.59/0.77  fof(f982,plain,(
% 2.59/0.77    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0)),
% 2.59/0.77    inference(resolution,[],[f534,f107])).
% 2.59/0.77  fof(f107,plain,(
% 2.59/0.77    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.59/0.77    inference(equality_resolution,[],[f70])).
% 3.17/0.77  fof(f70,plain,(
% 3.17/0.77    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.17/0.77    inference(cnf_transformation,[],[f39])).
% 3.17/0.77  fof(f39,plain,(
% 3.17/0.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.17/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 3.17/0.77  fof(f38,plain,(
% 3.17/0.77    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 3.17/0.77    introduced(choice_axiom,[])).
% 3.17/0.77  fof(f37,plain,(
% 3.17/0.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.17/0.77    inference(rectify,[],[f36])).
% 3.17/0.77  fof(f36,plain,(
% 3.17/0.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.17/0.77    inference(nnf_transformation,[],[f4])).
% 3.17/0.77  fof(f4,axiom,(
% 3.17/0.77    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.17/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 3.17/0.77  fof(f534,plain,(
% 3.17/0.77    r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 3.17/0.77    inference(equality_resolution,[],[f123])).
% 3.17/0.77  fof(f123,plain,(
% 3.17/0.77    ( ! [X2] : (sK0 != X2 | r2_hidden(sK2(k1_tarski(sK0),X2),k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),X2),X2) | k1_xboole_0 = k1_tarski(sK0)) )),
% 3.17/0.77    inference(superposition,[],[f55,f63])).
% 3.17/0.77  fof(f63,plain,(
% 3.17/0.77    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.17/0.77    inference(cnf_transformation,[],[f31])).
% 3.17/0.77  fof(f31,plain,(
% 3.17/0.77    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.17/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).
% 3.17/0.77  fof(f28,plain,(
% 3.17/0.77    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.17/0.77    introduced(choice_axiom,[])).
% 3.17/0.77  fof(f29,plain,(
% 3.17/0.77    ! [X1,X0] : (? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 3.17/0.77    introduced(choice_axiom,[])).
% 3.17/0.77  fof(f30,plain,(
% 3.17/0.77    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 3.17/0.77    introduced(choice_axiom,[])).
% 3.17/0.77  fof(f27,plain,(
% 3.17/0.77    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.17/0.77    inference(rectify,[],[f26])).
% 3.17/0.77  fof(f26,plain,(
% 3.17/0.77    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.17/0.77    inference(nnf_transformation,[],[f18])).
% 3.17/0.77  fof(f18,plain,(
% 3.17/0.77    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 3.17/0.77    inference(ennf_transformation,[],[f12])).
% 3.17/0.77  fof(f12,axiom,(
% 3.17/0.77    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 3.17/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 3.17/0.77  fof(f1009,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 3.17/0.77    inference(subsumption_resolution,[],[f1008,f106])).
% 3.17/0.77  fof(f1008,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 3.17/0.77    inference(subsumption_resolution,[],[f1007,f55])).
% 3.17/0.77  fof(f1007,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 3.17/0.77    inference(duplicate_literal_removal,[],[f997])).
% 3.17/0.77  fof(f997,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 3.17/0.77    inference(resolution,[],[f982,f62])).
% 3.17/0.77  fof(f62,plain,(
% 3.17/0.77    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.17/0.77    inference(cnf_transformation,[],[f31])).
% 3.17/0.77  fof(f64,plain,(
% 3.17/0.77    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.17/0.77    inference(cnf_transformation,[],[f31])).
% 3.17/0.77  fof(f1032,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 3.17/0.77    inference(subsumption_resolution,[],[f1031,f106])).
% 3.17/0.77  fof(f1031,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 3.17/0.77    inference(subsumption_resolution,[],[f1030,f55])).
% 3.17/0.77  fof(f1030,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 3.17/0.77    inference(duplicate_literal_removal,[],[f1020])).
% 3.17/0.77  fof(f1020,plain,(
% 3.17/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 3.17/0.77    inference(resolution,[],[f1019,f62])).
% 3.17/0.77  fof(f106,plain,(
% 3.17/0.77    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.17/0.77    inference(equality_resolution,[],[f105])).
% 3.17/0.77  fof(f105,plain,(
% 3.17/0.77    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.17/0.77    inference(equality_resolution,[],[f71])).
% 3.17/0.77  fof(f71,plain,(
% 3.17/0.77    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.17/0.77    inference(cnf_transformation,[],[f39])).
% 3.17/0.77  fof(f1076,plain,(
% 3.17/0.77    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | sK0 = X6) )),
% 3.17/0.77    inference(superposition,[],[f107,f1033])).
% 3.17/0.77  fof(f1086,plain,(
% 3.17/0.77    ~r2_hidden(sK0,sK6(k1_xboole_0))),
% 3.17/0.77    inference(resolution,[],[f1075,f119])).
% 3.17/0.77  fof(f119,plain,(
% 3.17/0.77    ( ! [X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) )),
% 3.17/0.77    inference(condensation,[],[f77])).
% 3.17/0.77  fof(f77,plain,(
% 3.17/0.77    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 3.17/0.77    inference(cnf_transformation,[],[f42])).
% 3.17/0.77  fof(f1079,plain,(
% 3.17/0.77    ( ! [X1] : (r2_hidden(sK0,X1) | ~r1_tarski(k1_xboole_0,X1)) )),
% 3.17/0.77    inference(resolution,[],[f1075,f67])).
% 3.17/0.77  fof(f67,plain,(
% 3.17/0.77    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.17/0.77    inference(cnf_transformation,[],[f35])).
% 3.17/0.77  fof(f35,plain,(
% 3.17/0.77    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 3.17/0.77  fof(f34,plain,(
% 3.17/0.77    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.17/0.77    introduced(choice_axiom,[])).
% 3.17/0.77  fof(f33,plain,(
% 3.17/0.77    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/0.77    inference(rectify,[],[f32])).
% 3.17/0.77  fof(f32,plain,(
% 3.17/0.77    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/0.77    inference(nnf_transformation,[],[f19])).
% 3.17/0.77  fof(f19,plain,(
% 3.17/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.17/0.77    inference(ennf_transformation,[],[f1])).
% 3.17/0.77  fof(f1,axiom,(
% 3.17/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.17/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.17/0.77  % SZS output end Proof for theBenchmark
% 3.17/0.77  % (20087)------------------------------
% 3.17/0.77  % (20087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.77  % (20087)Termination reason: Refutation
% 3.17/0.77  
% 3.17/0.77  % (20087)Memory used [KB]: 2686
% 3.17/0.77  % (20087)Time elapsed: 0.349 s
% 3.17/0.77  % (20087)------------------------------
% 3.17/0.77  % (20087)------------------------------
% 3.17/0.77  % (20063)Success in time 0.393 s
%------------------------------------------------------------------------------
