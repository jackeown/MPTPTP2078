%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:56 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 250 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 (1387 expanded)
%              Number of equality atoms :   40 ( 114 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(subsumption_resolution,[],[f547,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK2
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK2
      & r1_tarski(sK2,k3_subset_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f547,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f544,f540])).

fof(f540,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f528,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f528,plain,(
    ! [X0] : sP0(X0,X0,k1_xboole_0) ),
    inference(resolution,[],[f524,f56])).

fof(f56,plain,(
    ! [X6] : sP0(X6,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f48,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f524,plain,(
    ! [X10,X8,X9] :
      ( ~ sP0(X9,X10,X9)
      | sP0(X8,X8,X9) ) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,(
    ! [X10,X8,X9] :
      ( sP0(X8,X8,X9)
      | ~ sP0(X9,X10,X9)
      | sP0(X8,X8,X9) ) ),
    inference(resolution,[],[f516,f512])).

fof(f512,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f507])).

fof(f507,plain,(
    ! [X0,X1] :
      ( sP0(X0,X0,X1)
      | r2_hidden(sK4(X0,X0,X1),X1)
      | r2_hidden(sK4(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f516,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(sK4(X7,X7,X8),X9)
      | sP0(X7,X7,X8)
      | ~ sP0(X9,X10,X8) ) ),
    inference(resolution,[],[f512,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f544,plain,(
    ! [X2] : sK2 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f529,f47])).

fof(f529,plain,(
    ! [X1] : sP0(X1,X1,sK2) ),
    inference(resolution,[],[f524,f463])).

fof(f463,plain,(
    ! [X1] : sP0(X1,sK2,sK2) ),
    inference(resolution,[],[f459,f189])).

fof(f189,plain,(
    sP0(sK2,sK2,sK2) ),
    inference(superposition,[],[f107,f170])).

fof(f170,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f166,f96])).

fof(f96,plain,(
    ! [X0] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ) ),
    inference(resolution,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f166,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f130,f158])).

fof(f158,plain,(
    k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f130,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(forward_demodulation,[],[f128,f110])).

fof(f110,plain,(
    k4_xboole_0(sK2,sK3) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f34,f100])).

fof(f100,plain,(
    sK2 = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f96,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f128,plain,(
    k5_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(superposition,[],[f34,f118])).

fof(f118,plain,(
    sK2 = k3_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(superposition,[],[f97,f33])).

fof(f97,plain,(
    ! [X1] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X1,k3_subset_1(sK1,sK3))) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,(
    ! [X8] : sP0(k4_xboole_0(X8,sK3),sK2,sK2) ),
    inference(superposition,[],[f48,f96])).

fof(f459,plain,(
    ! [X6,X8,X7] :
      ( ~ sP0(X7,X8,X7)
      | sP0(X6,X7,X7) ) ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,(
    ! [X6,X8,X7] :
      ( sP0(X6,X7,X7)
      | ~ sP0(X7,X8,X7)
      | sP0(X6,X7,X7) ) ),
    inference(resolution,[],[f353,f351])).

fof(f351,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f43])).

fof(f353,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK4(X4,X5,X5),X6)
      | sP0(X4,X5,X5)
      | ~ sP0(X6,X7,X5) ) ),
    inference(resolution,[],[f351,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (14131)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (14108)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (14120)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (14115)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (14108)Refutation not found, incomplete strategy% (14108)------------------------------
% 0.21/0.50  % (14108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14108)Memory used [KB]: 1663
% 0.21/0.50  % (14108)Time elapsed: 0.093 s
% 0.21/0.50  % (14108)------------------------------
% 0.21/0.50  % (14108)------------------------------
% 0.21/0.50  % (14112)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (14136)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (14112)Refutation not found, incomplete strategy% (14112)------------------------------
% 0.21/0.51  % (14112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14112)Memory used [KB]: 6268
% 0.21/0.51  % (14112)Time elapsed: 0.103 s
% 0.21/0.51  % (14112)------------------------------
% 0.21/0.51  % (14112)------------------------------
% 0.21/0.51  % (14122)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (14134)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (14121)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (14114)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (14128)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (14126)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (14130)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.52  % (14130)Refutation not found, incomplete strategy% (14130)------------------------------
% 1.32/0.52  % (14130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (14130)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.52  
% 1.32/0.52  % (14130)Memory used [KB]: 10618
% 1.32/0.52  % (14130)Time elapsed: 0.090 s
% 1.32/0.52  % (14130)------------------------------
% 1.32/0.52  % (14130)------------------------------
% 1.32/0.52  % (14128)Refutation not found, incomplete strategy% (14128)------------------------------
% 1.32/0.52  % (14128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (14118)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.53  % (14118)Refutation not found, incomplete strategy% (14118)------------------------------
% 1.32/0.53  % (14118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (14118)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (14118)Memory used [KB]: 10618
% 1.32/0.53  % (14118)Time elapsed: 0.126 s
% 1.32/0.53  % (14118)------------------------------
% 1.32/0.53  % (14118)------------------------------
% 1.32/0.53  % (14132)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.53  % (14111)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (14135)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.53  % (14110)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (14128)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (14128)Memory used [KB]: 10746
% 1.32/0.53  % (14128)Time elapsed: 0.116 s
% 1.32/0.53  % (14128)------------------------------
% 1.32/0.53  % (14128)------------------------------
% 1.32/0.53  % (14109)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (14113)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (14133)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.54  % (14127)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.54  % (14124)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.54  % (14115)Refutation found. Thanks to Tanya!
% 1.46/0.54  % SZS status Theorem for theBenchmark
% 1.46/0.54  % SZS output start Proof for theBenchmark
% 1.46/0.54  fof(f548,plain,(
% 1.46/0.54    $false),
% 1.46/0.54    inference(subsumption_resolution,[],[f547,f31])).
% 1.46/0.54  fof(f31,plain,(
% 1.46/0.54    k1_xboole_0 != sK2),
% 1.46/0.54    inference(cnf_transformation,[],[f21])).
% 1.46/0.54  fof(f21,plain,(
% 1.46/0.54    k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.46/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f20])).
% 1.46/0.54  fof(f20,plain,(
% 1.46/0.54    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f13,plain,(
% 1.46/0.54    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.46/0.54    inference(flattening,[],[f12])).
% 1.46/0.54  fof(f12,plain,(
% 1.46/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.46/0.54    inference(ennf_transformation,[],[f10])).
% 1.46/0.54  fof(f10,negated_conjecture,(
% 1.46/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.46/0.54    inference(negated_conjecture,[],[f9])).
% 1.46/0.54  fof(f9,conjecture,(
% 1.46/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.46/0.54  fof(f547,plain,(
% 1.46/0.54    k1_xboole_0 = sK2),
% 1.46/0.54    inference(forward_demodulation,[],[f544,f540])).
% 1.46/0.54  fof(f540,plain,(
% 1.46/0.54    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.46/0.54    inference(resolution,[],[f528,f47])).
% 1.46/0.54  fof(f47,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.46/0.54    inference(cnf_transformation,[],[f27])).
% 1.46/0.54  fof(f27,plain,(
% 1.46/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.46/0.54    inference(nnf_transformation,[],[f19])).
% 1.46/0.54  fof(f19,plain,(
% 1.46/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.46/0.54    inference(definition_folding,[],[f1,f18])).
% 1.46/0.54  fof(f18,plain,(
% 1.46/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.46/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.46/0.54  fof(f1,axiom,(
% 1.46/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.46/0.54  fof(f528,plain,(
% 1.46/0.54    ( ! [X0] : (sP0(X0,X0,k1_xboole_0)) )),
% 1.46/0.54    inference(resolution,[],[f524,f56])).
% 1.46/0.54  fof(f56,plain,(
% 1.46/0.54    ( ! [X6] : (sP0(X6,k1_xboole_0,k1_xboole_0)) )),
% 1.46/0.54    inference(superposition,[],[f48,f52])).
% 1.46/0.54  fof(f52,plain,(
% 1.46/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.46/0.54    inference(resolution,[],[f51,f36])).
% 1.46/0.54  fof(f36,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.46/0.54    inference(cnf_transformation,[],[f15])).
% 1.46/0.54  fof(f15,plain,(
% 1.46/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.46/0.54    inference(ennf_transformation,[],[f11])).
% 1.46/0.54  fof(f11,plain,(
% 1.46/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.46/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 1.46/0.54  fof(f6,axiom,(
% 1.46/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.46/0.54  fof(f51,plain,(
% 1.46/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.46/0.54    inference(resolution,[],[f39,f32])).
% 1.46/0.54  fof(f32,plain,(
% 1.46/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f4])).
% 1.46/0.54  fof(f4,axiom,(
% 1.46/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.46/0.54  fof(f39,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f17])).
% 1.46/0.54  fof(f17,plain,(
% 1.46/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.46/0.54    inference(ennf_transformation,[],[f3])).
% 1.46/0.54  fof(f3,axiom,(
% 1.46/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.46/0.54  fof(f48,plain,(
% 1.46/0.54    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.46/0.54    inference(equality_resolution,[],[f46])).
% 1.46/0.54  fof(f46,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.46/0.54    inference(cnf_transformation,[],[f27])).
% 1.46/0.54  fof(f524,plain,(
% 1.46/0.54    ( ! [X10,X8,X9] : (~sP0(X9,X10,X9) | sP0(X8,X8,X9)) )),
% 1.46/0.54    inference(duplicate_literal_removal,[],[f523])).
% 1.46/0.54  fof(f523,plain,(
% 1.46/0.54    ( ! [X10,X8,X9] : (sP0(X8,X8,X9) | ~sP0(X9,X10,X9) | sP0(X8,X8,X9)) )),
% 1.46/0.54    inference(resolution,[],[f516,f512])).
% 1.46/0.54  fof(f512,plain,(
% 1.46/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 1.46/0.54    inference(duplicate_literal_removal,[],[f507])).
% 1.46/0.54  fof(f507,plain,(
% 1.46/0.54    ( ! [X0,X1] : (sP0(X0,X0,X1) | r2_hidden(sK4(X0,X0,X1),X1) | r2_hidden(sK4(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 1.46/0.54    inference(resolution,[],[f44,f43])).
% 1.46/0.54  fof(f43,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f26])).
% 1.46/0.54  fof(f26,plain,(
% 1.46/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.46/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.46/0.54  fof(f25,plain,(
% 1.46/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f24,plain,(
% 1.46/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.46/0.54    inference(rectify,[],[f23])).
% 1.46/0.54  fof(f23,plain,(
% 1.46/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.46/0.54    inference(flattening,[],[f22])).
% 1.46/0.54  fof(f22,plain,(
% 1.46/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.46/0.54    inference(nnf_transformation,[],[f18])).
% 1.46/0.54  fof(f44,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f26])).
% 1.46/0.54  fof(f516,plain,(
% 1.46/0.54    ( ! [X10,X8,X7,X9] : (~r2_hidden(sK4(X7,X7,X8),X9) | sP0(X7,X7,X8) | ~sP0(X9,X10,X8)) )),
% 1.46/0.54    inference(resolution,[],[f512,f41])).
% 1.46/0.54  fof(f41,plain,(
% 1.46/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f26])).
% 1.46/0.54  fof(f544,plain,(
% 1.46/0.54    ( ! [X2] : (sK2 = k4_xboole_0(X2,X2)) )),
% 1.46/0.54    inference(resolution,[],[f529,f47])).
% 1.46/0.54  fof(f529,plain,(
% 1.46/0.54    ( ! [X1] : (sP0(X1,X1,sK2)) )),
% 1.46/0.54    inference(resolution,[],[f524,f463])).
% 1.46/0.54  fof(f463,plain,(
% 1.46/0.54    ( ! [X1] : (sP0(X1,sK2,sK2)) )),
% 1.46/0.54    inference(resolution,[],[f459,f189])).
% 1.46/0.54  fof(f189,plain,(
% 1.46/0.54    sP0(sK2,sK2,sK2)),
% 1.46/0.54    inference(superposition,[],[f107,f170])).
% 1.46/0.54  fof(f170,plain,(
% 1.46/0.54    sK2 = k4_xboole_0(sK2,sK3)),
% 1.46/0.54    inference(forward_demodulation,[],[f166,f96])).
% 1.46/0.54  fof(f96,plain,(
% 1.46/0.54    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X0,sK3))) )),
% 1.46/0.54    inference(resolution,[],[f49,f29])).
% 1.46/0.54  fof(f29,plain,(
% 1.46/0.54    r1_tarski(sK2,sK3)),
% 1.46/0.54    inference(cnf_transformation,[],[f21])).
% 1.46/0.54  fof(f49,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) )),
% 1.46/0.54    inference(resolution,[],[f37,f36])).
% 1.46/0.54  fof(f37,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f16])).
% 1.46/0.54  fof(f16,plain,(
% 1.46/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.46/0.54    inference(ennf_transformation,[],[f7])).
% 1.46/0.54  fof(f7,axiom,(
% 1.46/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.46/0.54  fof(f166,plain,(
% 1.46/0.54    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))),
% 1.46/0.54    inference(backward_demodulation,[],[f130,f158])).
% 1.46/0.54  fof(f158,plain,(
% 1.46/0.54    k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3)),
% 1.46/0.54    inference(resolution,[],[f35,f28])).
% 1.46/0.54  fof(f28,plain,(
% 1.46/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.46/0.54    inference(cnf_transformation,[],[f21])).
% 1.46/0.54  fof(f35,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f14])).
% 1.46/0.54  fof(f14,plain,(
% 1.46/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.46/0.54    inference(ennf_transformation,[],[f8])).
% 1.46/0.54  fof(f8,axiom,(
% 1.46/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.46/0.54  fof(f130,plain,(
% 1.46/0.54    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 1.46/0.54    inference(forward_demodulation,[],[f128,f110])).
% 1.46/0.54  fof(f110,plain,(
% 1.46/0.54    k4_xboole_0(sK2,sK3) = k5_xboole_0(sK2,sK2)),
% 1.46/0.54    inference(superposition,[],[f34,f100])).
% 1.46/0.54  fof(f100,plain,(
% 1.46/0.54    sK2 = k3_xboole_0(sK2,sK3)),
% 1.46/0.54    inference(superposition,[],[f96,f33])).
% 1.46/0.54  fof(f33,plain,(
% 1.46/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f5])).
% 1.46/0.54  fof(f5,axiom,(
% 1.46/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.46/0.54  fof(f34,plain,(
% 1.46/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f2])).
% 1.46/0.54  fof(f2,axiom,(
% 1.46/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.46/0.54  fof(f128,plain,(
% 1.46/0.54    k5_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 1.46/0.54    inference(superposition,[],[f34,f118])).
% 1.46/0.54  fof(f118,plain,(
% 1.46/0.54    sK2 = k3_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 1.46/0.54    inference(superposition,[],[f97,f33])).
% 1.46/0.54  fof(f97,plain,(
% 1.46/0.54    ( ! [X1] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X1,k3_subset_1(sK1,sK3)))) )),
% 1.46/0.54    inference(resolution,[],[f49,f30])).
% 1.46/0.54  fof(f30,plain,(
% 1.46/0.54    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 1.46/0.54    inference(cnf_transformation,[],[f21])).
% 1.46/0.54  fof(f107,plain,(
% 1.46/0.54    ( ! [X8] : (sP0(k4_xboole_0(X8,sK3),sK2,sK2)) )),
% 1.46/0.54    inference(superposition,[],[f48,f96])).
% 1.46/0.54  fof(f459,plain,(
% 1.46/0.54    ( ! [X6,X8,X7] : (~sP0(X7,X8,X7) | sP0(X6,X7,X7)) )),
% 1.46/0.54    inference(duplicate_literal_removal,[],[f458])).
% 1.46/0.54  fof(f458,plain,(
% 1.46/0.54    ( ! [X6,X8,X7] : (sP0(X6,X7,X7) | ~sP0(X7,X8,X7) | sP0(X6,X7,X7)) )),
% 1.46/0.54    inference(resolution,[],[f353,f351])).
% 1.46/0.54  fof(f351,plain,(
% 1.46/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.46/0.54    inference(factoring,[],[f43])).
% 1.46/0.54  fof(f353,plain,(
% 1.46/0.54    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK4(X4,X5,X5),X6) | sP0(X4,X5,X5) | ~sP0(X6,X7,X5)) )),
% 1.46/0.54    inference(resolution,[],[f351,f41])).
% 1.46/0.54  % SZS output end Proof for theBenchmark
% 1.46/0.54  % (14115)------------------------------
% 1.46/0.54  % (14115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (14115)Termination reason: Refutation
% 1.46/0.54  
% 1.46/0.54  % (14115)Memory used [KB]: 6524
% 1.46/0.54  % (14115)Time elapsed: 0.133 s
% 1.46/0.54  % (14115)------------------------------
% 1.46/0.54  % (14115)------------------------------
% 1.46/0.54  % (14107)Success in time 0.181 s
%------------------------------------------------------------------------------
