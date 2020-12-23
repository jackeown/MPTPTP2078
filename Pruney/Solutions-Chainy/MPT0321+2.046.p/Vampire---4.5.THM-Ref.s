%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 (2366 expanded)
%              Number of leaves         :    7 ( 534 expanded)
%              Depth                    :   40
%              Number of atoms          :  341 (18182 expanded)
%              Number of equality atoms :  120 (3853 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1725,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1703,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f1703,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1701,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f8,f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1701,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(subsumption_resolution,[],[f1700,f1289])).

fof(f1289,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f1108])).

fof(f1108,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f23,f1106])).

fof(f1106,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f1080,f21])).

fof(f1080,plain,
    ( sK0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1041,f24])).

fof(f1041,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK0 = sK2 ) ),
    inference(resolution,[],[f1039,f532])).

fof(f532,plain,(
    ! [X11] :
      ( r2_hidden(sK4(sK1),sK3)
      | ~ r2_hidden(X11,sK0) ) ),
    inference(subsumption_resolution,[],[f518,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f518,plain,(
    ! [X11] :
      ( r2_hidden(sK4(sK1),sK3)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X11,sK0) ) ),
    inference(superposition,[],[f37,f512])).

fof(f512,plain,(
    ! [X0] :
      ( sK1 = k3_xboole_0(sK1,sK3)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f511,f101])).

fof(f101,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,X6),X7)
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f98,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f98,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,X6),X7)
      | ~ r2_hidden(sK5(X6,X7,X6),X6)
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,X6),X7)
      | ~ r2_hidden(sK5(X6,X7,X6),X6)
      | k3_xboole_0(X6,X7) = X6
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(resolution,[],[f30,f58])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f511,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = k3_xboole_0(sK1,sK3)
      | r2_hidden(sK5(sK1,sK3,sK1),sK3) ) ),
    inference(duplicate_literal_removal,[],[f499])).

fof(f499,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = k3_xboole_0(sK1,sK3)
      | r2_hidden(sK5(sK1,sK3,sK1),sK3)
      | sK1 = k3_xboole_0(sK1,sK3) ) ),
    inference(resolution,[],[f117,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(sK5(X17,sK3,X17),sK1)
      | ~ r2_hidden(X18,sK0)
      | k3_xboole_0(X17,sK3) = X17 ) ),
    inference(resolution,[],[f101,f49])).

fof(f49,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK0)
      | ~ r2_hidden(X8,sK1) ) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X1,sK3) ) ),
    inference(superposition,[],[f32,f20])).

fof(f20,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1039,plain,(
    ! [X27] :
      ( ~ r2_hidden(X27,sK3)
      | sK0 = sK2 ) ),
    inference(subsumption_resolution,[],[f1014,f22])).

fof(f1014,plain,(
    ! [X27] :
      ( ~ r2_hidden(X27,sK3)
      | sK0 = sK2
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f1004,f24])).

fof(f1004,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK3)
      | sK0 = sK2 ) ),
    inference(forward_demodulation,[],[f1003,f121])).

fof(f121,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2] :
      ( k3_xboole_0(X2,X2) = X2
      | k3_xboole_0(X2,X2) = X2 ) ),
    inference(resolution,[],[f101,f58])).

fof(f1003,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | sK2 = k3_xboole_0(sK0,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(condensation,[],[f1002])).

fof(f1002,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | sK2 = k3_xboole_0(sK0,sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X2,sK3) ) ),
    inference(duplicate_literal_removal,[],[f983])).

fof(f983,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | sK2 = k3_xboole_0(sK0,sK0)
      | ~ r2_hidden(X1,sK1)
      | sK2 = k3_xboole_0(sK0,sK0)
      | ~ r2_hidden(X2,sK3) ) ),
    inference(resolution,[],[f982,f976])).

fof(f976,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK0,X0,sK2),sK0)
      | sK2 = k3_xboole_0(sK0,X0)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(factoring,[],[f623])).

fof(f623,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,sK2),sK0)
      | k3_xboole_0(X0,X1) = sK2
      | r2_hidden(sK5(X0,X1,sK2),X0)
      | ~ r2_hidden(X2,sK3) ) ),
    inference(superposition,[],[f57,f135])).

fof(f135,plain,(
    ! [X0] :
      ( sK2 = k3_xboole_0(sK2,sK0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f134,f101])).

fof(f134,plain,(
    ! [X0] :
      ( sK2 = k3_xboole_0(sK2,sK0)
      | ~ r2_hidden(X0,sK3)
      | r2_hidden(sK5(sK2,sK0,sK2),sK0) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( sK2 = k3_xboole_0(sK2,sK0)
      | ~ r2_hidden(X0,sK3)
      | r2_hidden(sK5(sK2,sK0,sK2),sK0)
      | sK2 = k3_xboole_0(sK2,sK0) ) ),
    inference(resolution,[],[f114,f29])).

fof(f114,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(sK5(X11,sK0,X11),sK2)
      | k3_xboole_0(X11,sK0) = X11
      | ~ r2_hidden(X12,sK3) ) ),
    inference(resolution,[],[f101,f55])).

fof(f55,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,sK0)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X6,sK3) ) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f33,f20])).

fof(f57,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK5(X4,X5,k3_xboole_0(X6,X7)),X7)
      | k3_xboole_0(X4,X5) = k3_xboole_0(X6,X7)
      | r2_hidden(sK5(X4,X5,k3_xboole_0(X6,X7)),X4) ) ),
    inference(resolution,[],[f28,f35])).

fof(f982,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(sK0,X0,sK2),X0)
      | ~ r2_hidden(X1,sK3)
      | sK2 = k3_xboole_0(sK0,X0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f981,f976])).

fof(f981,plain,(
    ! [X2,X0,X1] :
      ( sK2 = k3_xboole_0(sK0,X0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(sK5(sK0,X0,sK2),sK0)
      | ~ r2_hidden(sK5(sK0,X0,sK2),X0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f980])).

fof(f980,plain,(
    ! [X2,X0,X1] :
      ( sK2 = k3_xboole_0(sK0,X0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(sK5(sK0,X0,sK2),sK0)
      | sK2 = k3_xboole_0(sK0,X0)
      | ~ r2_hidden(sK5(sK0,X0,sK2),X0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f976,f95])).

fof(f95,plain,(
    ! [X21,X22,X20] :
      ( ~ r2_hidden(sK5(X20,X21,sK2),sK0)
      | ~ r2_hidden(sK5(X20,X21,sK2),X20)
      | sK2 = k3_xboole_0(X20,X21)
      | ~ r2_hidden(sK5(X20,X21,sK2),X21)
      | ~ r2_hidden(X22,sK1) ) ),
    inference(resolution,[],[f30,f50])).

fof(f50,plain,(
    ! [X10,X11] :
      ( r2_hidden(X11,sK2)
      | ~ r2_hidden(X11,sK0)
      | ~ r2_hidden(X10,sK1) ) ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f31,f20])).

fof(f23,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f1700,plain,(
    ! [X0] :
      ( sK1 = sK3
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f1699,f121])).

fof(f1699,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK3 = k3_xboole_0(sK1,sK1) ) ),
    inference(condensation,[],[f1698])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( sK3 = k3_xboole_0(sK1,sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f1683])).

fof(f1683,plain,(
    ! [X0,X1] :
      ( sK3 = k3_xboole_0(sK1,sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | sK3 = k3_xboole_0(sK1,sK1) ) ),
    inference(resolution,[],[f1682,f1674])).

fof(f1674,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK1,X0,sK3),sK1)
      | ~ r2_hidden(X1,sK0)
      | sK3 = k3_xboole_0(sK1,X0) ) ),
    inference(factoring,[],[f1265])).

fof(f1265,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(sK5(X11,X12,sK3),sK1)
      | ~ r2_hidden(X13,sK0)
      | sK3 = k3_xboole_0(X11,X12)
      | r2_hidden(sK5(X11,X12,sK3),X11) ) ),
    inference(backward_demodulation,[],[f626,f1106])).

fof(f626,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(sK5(X11,X12,sK3),sK1)
      | sK3 = k3_xboole_0(X11,X12)
      | r2_hidden(sK5(X11,X12,sK3),X11)
      | ~ r2_hidden(X13,sK2) ) ),
    inference(superposition,[],[f57,f247])).

fof(f247,plain,(
    ! [X0] :
      ( sK3 = k3_xboole_0(sK3,sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f246,f101])).

fof(f246,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK3 = k3_xboole_0(sK3,sK1)
      | r2_hidden(sK5(sK3,sK1,sK3),sK1) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK3 = k3_xboole_0(sK3,sK1)
      | r2_hidden(sK5(sK3,sK1,sK3),sK1)
      | sK3 = k3_xboole_0(sK3,sK1) ) ),
    inference(resolution,[],[f115,f29])).

fof(f115,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(sK5(X13,sK1,X13),sK3)
      | ~ r2_hidden(X14,sK2)
      | k3_xboole_0(X13,sK1) = X13 ) ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(resolution,[],[f51,f32])).

fof(f1682,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(sK1,X1,sK3),X1)
      | sK3 = k3_xboole_0(sK1,X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f1681,f1674])).

fof(f1681,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | sK3 = k3_xboole_0(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1,sK3),sK1)
      | ~ r2_hidden(sK5(sK1,X1,sK3),X1) ) ),
    inference(condensation,[],[f1680])).

fof(f1680,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | sK3 = k3_xboole_0(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1,sK3),sK1)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(sK5(sK1,X1,sK3),X1) ) ),
    inference(duplicate_literal_removal,[],[f1679])).

fof(f1679,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | sK3 = k3_xboole_0(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1,sK3),sK1)
      | sK3 = k3_xboole_0(sK1,X1)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(sK5(sK1,X1,sK3),X1) ) ),
    inference(resolution,[],[f1674,f96])).

fof(f96,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(sK5(X23,X24,sK3),sK1)
      | ~ r2_hidden(sK5(X23,X24,sK3),X23)
      | sK3 = k3_xboole_0(X23,X24)
      | ~ r2_hidden(X25,sK0)
      | ~ r2_hidden(sK5(X23,X24,sK3),X24) ) ),
    inference(resolution,[],[f30,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (21250)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (21258)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (21245)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (21246)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (21256)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (21251)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (21242)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (21259)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (21242)Refutation not found, incomplete strategy% (21242)------------------------------
% 0.21/0.52  % (21242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21242)Memory used [KB]: 10618
% 0.21/0.52  % (21242)Time elapsed: 0.094 s
% 0.21/0.52  % (21242)------------------------------
% 0.21/0.52  % (21242)------------------------------
% 0.21/0.53  % (21251)Refutation not found, incomplete strategy% (21251)------------------------------
% 0.21/0.53  % (21251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21251)Memory used [KB]: 6012
% 0.21/0.53  % (21251)Time elapsed: 0.097 s
% 0.21/0.53  % (21251)------------------------------
% 0.21/0.53  % (21251)------------------------------
% 0.21/0.53  % (21241)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (21241)Refutation not found, incomplete strategy% (21241)------------------------------
% 0.21/0.53  % (21241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21241)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21241)Memory used [KB]: 6140
% 0.21/0.53  % (21241)Time elapsed: 0.106 s
% 0.21/0.53  % (21241)------------------------------
% 0.21/0.53  % (21241)------------------------------
% 0.21/0.53  % (21257)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.54  % (21261)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (21247)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.54  % (21244)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (21261)Refutation not found, incomplete strategy% (21261)------------------------------
% 0.21/0.54  % (21261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21261)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21261)Memory used [KB]: 10490
% 0.21/0.54  % (21261)Time elapsed: 0.109 s
% 0.21/0.54  % (21261)------------------------------
% 0.21/0.54  % (21261)------------------------------
% 0.21/0.54  % (21244)Refutation not found, incomplete strategy% (21244)------------------------------
% 0.21/0.54  % (21244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21244)Memory used [KB]: 10618
% 0.21/0.54  % (21244)Time elapsed: 0.112 s
% 0.21/0.54  % (21244)------------------------------
% 0.21/0.54  % (21244)------------------------------
% 0.21/0.54  % (21249)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.54  % (21243)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (21248)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.55  % (21254)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.55  % (21255)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.55  % (21252)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.55  % (21253)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (21260)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.57  % (21259)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1725,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f1703,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f6])).
% 0.21/0.57  fof(f6,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    inference(negated_conjecture,[],[f4])).
% 0.21/0.57  fof(f4,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.57  fof(f1703,plain,(
% 0.21/0.57    k1_xboole_0 = sK0),
% 0.21/0.57    inference(resolution,[],[f1701,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f8,f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.57  fof(f1701,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f1700,f1289])).
% 0.21/0.57  fof(f1289,plain,(
% 0.21/0.57    sK1 != sK3),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f1108])).
% 0.21/0.57  fof(f1108,plain,(
% 0.21/0.57    sK0 != sK0 | sK1 != sK3),
% 0.21/0.57    inference(backward_demodulation,[],[f23,f1106])).
% 0.21/0.57  fof(f1106,plain,(
% 0.21/0.57    sK0 = sK2),
% 0.21/0.57    inference(subsumption_resolution,[],[f1080,f21])).
% 0.21/0.57  fof(f1080,plain,(
% 0.21/0.57    sK0 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.57    inference(resolution,[],[f1041,f24])).
% 0.21/0.57  fof(f1041,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_hidden(X2,sK0) | sK0 = sK2) )),
% 0.21/0.57    inference(resolution,[],[f1039,f532])).
% 0.21/0.57  fof(f532,plain,(
% 0.21/0.57    ( ! [X11] : (r2_hidden(sK4(sK1),sK3) | ~r2_hidden(X11,sK0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f518,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f518,plain,(
% 0.21/0.57    ( ! [X11] : (r2_hidden(sK4(sK1),sK3) | k1_xboole_0 = sK1 | ~r2_hidden(X11,sK0)) )),
% 0.21/0.57    inference(superposition,[],[f37,f512])).
% 0.21/0.57  fof(f512,plain,(
% 0.21/0.57    ( ! [X0] : (sK1 = k3_xboole_0(sK1,sK3) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f511,f101])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,X6),X7) | k3_xboole_0(X6,X7) = X6) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f98,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.57    inference(factoring,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(flattening,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,X6),X7) | ~r2_hidden(sK5(X6,X7,X6),X6) | k3_xboole_0(X6,X7) = X6) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,X6),X7) | ~r2_hidden(sK5(X6,X7,X6),X6) | k3_xboole_0(X6,X7) = X6 | k3_xboole_0(X6,X7) = X6) )),
% 0.21/0.57    inference(resolution,[],[f30,f58])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f511,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k3_xboole_0(sK1,sK3) | r2_hidden(sK5(sK1,sK3,sK1),sK3)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f499])).
% 0.21/0.57  fof(f499,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k3_xboole_0(sK1,sK3) | r2_hidden(sK5(sK1,sK3,sK1),sK3) | sK1 = k3_xboole_0(sK1,sK3)) )),
% 0.21/0.57    inference(resolution,[],[f117,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X17,X18] : (~r2_hidden(sK5(X17,sK3,X17),sK1) | ~r2_hidden(X18,sK0) | k3_xboole_0(X17,sK3) = X17) )),
% 0.21/0.57    inference(resolution,[],[f101,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X8,X9] : (r2_hidden(X8,sK3) | ~r2_hidden(X9,sK0) | ~r2_hidden(X8,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f33,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,sK3)) )),
% 0.21/0.57    inference(superposition,[],[f32,f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.57    inference(flattening,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.57    inference(nnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.57    inference(resolution,[],[f35,f24])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f1039,plain,(
% 0.21/0.57    ( ! [X27] : (~r2_hidden(X27,sK3) | sK0 = sK2) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f1014,f22])).
% 0.21/0.57  fof(f1014,plain,(
% 0.21/0.57    ( ! [X27] : (~r2_hidden(X27,sK3) | sK0 = sK2 | k1_xboole_0 = sK1) )),
% 0.21/0.57    inference(resolution,[],[f1004,f24])).
% 0.21/0.57  fof(f1004,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK3) | sK0 = sK2) )),
% 0.21/0.57    inference(forward_demodulation,[],[f1003,f121])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    ( ! [X2] : (k3_xboole_0(X2,X2) = X2 | k3_xboole_0(X2,X2) = X2) )),
% 0.21/0.57    inference(resolution,[],[f101,f58])).
% 0.21/0.57  fof(f1003,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | sK2 = k3_xboole_0(sK0,sK0) | ~r2_hidden(X1,sK1)) )),
% 0.21/0.57    inference(condensation,[],[f1002])).
% 0.21/0.57  fof(f1002,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | sK2 = k3_xboole_0(sK0,sK0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X2,sK3)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f983])).
% 0.21/0.57  fof(f983,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | sK2 = k3_xboole_0(sK0,sK0) | ~r2_hidden(X1,sK1) | sK2 = k3_xboole_0(sK0,sK0) | ~r2_hidden(X2,sK3)) )),
% 0.21/0.57    inference(resolution,[],[f982,f976])).
% 0.21/0.57  fof(f976,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,sK2),sK0) | sK2 = k3_xboole_0(sK0,X0) | ~r2_hidden(X1,sK3)) )),
% 0.21/0.57    inference(factoring,[],[f623])).
% 0.21/0.57  fof(f623,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,sK2),sK0) | k3_xboole_0(X0,X1) = sK2 | r2_hidden(sK5(X0,X1,sK2),X0) | ~r2_hidden(X2,sK3)) )),
% 0.21/0.57    inference(superposition,[],[f57,f135])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    ( ! [X0] : (sK2 = k3_xboole_0(sK2,sK0) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f134,f101])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X0] : (sK2 = k3_xboole_0(sK2,sK0) | ~r2_hidden(X0,sK3) | r2_hidden(sK5(sK2,sK0,sK2),sK0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ( ! [X0] : (sK2 = k3_xboole_0(sK2,sK0) | ~r2_hidden(X0,sK3) | r2_hidden(sK5(sK2,sK0,sK2),sK0) | sK2 = k3_xboole_0(sK2,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f114,f29])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    ( ! [X12,X11] : (~r2_hidden(sK5(X11,sK0,X11),sK2) | k3_xboole_0(X11,sK0) = X11 | ~r2_hidden(X12,sK3)) )),
% 0.21/0.57    inference(resolution,[],[f101,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X6,X7] : (r2_hidden(X7,sK0) | ~r2_hidden(X7,sK2) | ~r2_hidden(X6,sK3)) )),
% 0.21/0.57    inference(resolution,[],[f51,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.57    inference(superposition,[],[f33,f20])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X6,X4,X7,X5] : (r2_hidden(sK5(X4,X5,k3_xboole_0(X6,X7)),X7) | k3_xboole_0(X4,X5) = k3_xboole_0(X6,X7) | r2_hidden(sK5(X4,X5,k3_xboole_0(X6,X7)),X4)) )),
% 0.21/0.57    inference(resolution,[],[f28,f35])).
% 0.21/0.57  fof(f982,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK5(sK0,X0,sK2),X0) | ~r2_hidden(X1,sK3) | sK2 = k3_xboole_0(sK0,X0) | ~r2_hidden(X2,sK1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f981,f976])).
% 0.21/0.57  fof(f981,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sK2 = k3_xboole_0(sK0,X0) | ~r2_hidden(X1,sK3) | ~r2_hidden(sK5(sK0,X0,sK2),sK0) | ~r2_hidden(sK5(sK0,X0,sK2),X0) | ~r2_hidden(X2,sK1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f980])).
% 0.21/0.57  fof(f980,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sK2 = k3_xboole_0(sK0,X0) | ~r2_hidden(X1,sK3) | ~r2_hidden(sK5(sK0,X0,sK2),sK0) | sK2 = k3_xboole_0(sK0,X0) | ~r2_hidden(sK5(sK0,X0,sK2),X0) | ~r2_hidden(X2,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f976,f95])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    ( ! [X21,X22,X20] : (~r2_hidden(sK5(X20,X21,sK2),sK0) | ~r2_hidden(sK5(X20,X21,sK2),X20) | sK2 = k3_xboole_0(X20,X21) | ~r2_hidden(sK5(X20,X21,sK2),X21) | ~r2_hidden(X22,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f30,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X10,X11] : (r2_hidden(X11,sK2) | ~r2_hidden(X11,sK0) | ~r2_hidden(X10,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f33,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) )),
% 0.21/0.57    inference(superposition,[],[f31,f20])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    sK1 != sK3 | sK0 != sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f1700,plain,(
% 0.21/0.57    ( ! [X0] : (sK1 = sK3 | ~r2_hidden(X0,sK0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f1699,f121])).
% 0.21/0.57  fof(f1699,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | sK3 = k3_xboole_0(sK1,sK1)) )),
% 0.21/0.57    inference(condensation,[],[f1698])).
% 0.21/0.57  fof(f1698,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sK3 = k3_xboole_0(sK1,sK1) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f1683])).
% 0.21/0.57  fof(f1683,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sK3 = k3_xboole_0(sK1,sK1) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | sK3 = k3_xboole_0(sK1,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f1682,f1674])).
% 0.21/0.57  fof(f1674,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK5(sK1,X0,sK3),sK1) | ~r2_hidden(X1,sK0) | sK3 = k3_xboole_0(sK1,X0)) )),
% 0.21/0.57    inference(factoring,[],[f1265])).
% 0.21/0.57  fof(f1265,plain,(
% 0.21/0.57    ( ! [X12,X13,X11] : (r2_hidden(sK5(X11,X12,sK3),sK1) | ~r2_hidden(X13,sK0) | sK3 = k3_xboole_0(X11,X12) | r2_hidden(sK5(X11,X12,sK3),X11)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f626,f1106])).
% 0.21/0.57  fof(f626,plain,(
% 0.21/0.57    ( ! [X12,X13,X11] : (r2_hidden(sK5(X11,X12,sK3),sK1) | sK3 = k3_xboole_0(X11,X12) | r2_hidden(sK5(X11,X12,sK3),X11) | ~r2_hidden(X13,sK2)) )),
% 0.21/0.57    inference(superposition,[],[f57,f247])).
% 0.21/0.57  fof(f247,plain,(
% 0.21/0.57    ( ! [X0] : (sK3 = k3_xboole_0(sK3,sK1) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f246,f101])).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | sK3 = k3_xboole_0(sK3,sK1) | r2_hidden(sK5(sK3,sK1,sK3),sK1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f236])).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | sK3 = k3_xboole_0(sK3,sK1) | r2_hidden(sK5(sK3,sK1,sK3),sK1) | sK3 = k3_xboole_0(sK3,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f115,f29])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X14,X13] : (~r2_hidden(sK5(X13,sK1,X13),sK3) | ~r2_hidden(X14,sK2) | k3_xboole_0(X13,sK1) = X13) )),
% 0.21/0.57    inference(resolution,[],[f101,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X4,X5] : (r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK3)) )),
% 0.21/0.57    inference(resolution,[],[f51,f32])).
% 0.21/0.57  fof(f1682,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(sK1,X1,sK3),X1) | sK3 = k3_xboole_0(sK1,X1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f1681,f1674])).
% 0.21/0.57  fof(f1681,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | sK3 = k3_xboole_0(sK1,X1) | ~r2_hidden(sK5(sK1,X1,sK3),sK1) | ~r2_hidden(sK5(sK1,X1,sK3),X1)) )),
% 0.21/0.57    inference(condensation,[],[f1680])).
% 0.21/0.57  fof(f1680,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | sK3 = k3_xboole_0(sK1,X1) | ~r2_hidden(sK5(sK1,X1,sK3),sK1) | ~r2_hidden(X2,sK0) | ~r2_hidden(sK5(sK1,X1,sK3),X1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f1679])).
% 0.21/0.57  fof(f1679,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | sK3 = k3_xboole_0(sK1,X1) | ~r2_hidden(sK5(sK1,X1,sK3),sK1) | sK3 = k3_xboole_0(sK1,X1) | ~r2_hidden(X2,sK0) | ~r2_hidden(sK5(sK1,X1,sK3),X1)) )),
% 0.21/0.57    inference(resolution,[],[f1674,f96])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X24,X23,X25] : (~r2_hidden(sK5(X23,X24,sK3),sK1) | ~r2_hidden(sK5(X23,X24,sK3),X23) | sK3 = k3_xboole_0(X23,X24) | ~r2_hidden(X25,sK0) | ~r2_hidden(sK5(X23,X24,sK3),X24)) )),
% 0.21/0.57    inference(resolution,[],[f30,f49])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (21259)------------------------------
% 0.21/0.57  % (21259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21259)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (21259)Memory used [KB]: 2942
% 0.21/0.57  % (21259)Time elapsed: 0.135 s
% 0.21/0.57  % (21259)------------------------------
% 0.21/0.57  % (21259)------------------------------
% 0.21/0.58  % (21240)Success in time 0.21 s
%------------------------------------------------------------------------------
