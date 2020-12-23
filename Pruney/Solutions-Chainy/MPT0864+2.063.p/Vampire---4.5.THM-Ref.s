%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 599 expanded)
%              Number of leaves         :   21 ( 201 expanded)
%              Depth                    :   18
%              Number of atoms          :  297 (1036 expanded)
%              Number of equality atoms :  242 ( 945 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(subsumption_resolution,[],[f230,f114])).

fof(f114,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f113,f48])).

% (11085)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (11075)Termination reason: Refutation not found, incomplete strategy

% (11075)Memory used [KB]: 6140
% (11075)Time elapsed: 0.006 s
% (11075)------------------------------
% (11075)------------------------------
% (11062)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (11063)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

% (11074)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f113,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f99,f80])).

fof(f80,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f77,f75,f77,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f99,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f44,f77,f76,f77,f77])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f230,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f218,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f218,plain,(
    ! [X0] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(backward_demodulation,[],[f181,f212])).

fof(f212,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f210,f124])).

fof(f124,plain,(
    ! [X6,X10,X8,X7,X11,X9] : r1_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X7,X7,X7,X8,X9,X10,X6,X11)) ),
    inference(resolution,[],[f83,f103])).

fof(f103,plain,(
    ! [X2,X0,X8,X5,X3,X1] : r2_hidden(X8,k6_enumset1(X0,X0,X0,X1,X2,X3,X8,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X6,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X8,X5) != X6 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X4 != X8
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X4 != X8
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f210,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X0,sK0)))
      | sK0 = sK1 ) ),
    inference(superposition,[],[f209,f118])).

fof(f118,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f116,f117])).

fof(f117,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f116,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f34,f115])).

fof(f115,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f209,plain,(
    ! [X3] : ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X3,sK2))) ),
    inference(subsumption_resolution,[],[f203,f114])).

fof(f203,plain,(
    ! [X3] :
      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X3,sK2)))
      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ) ),
    inference(superposition,[],[f40,f141])).

fof(f141,plain,(
    ! [X0] : k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X0,sK2)) ),
    inference(superposition,[],[f78,f33])).

fof(f78,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f38,f74,f77,f74])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f181,plain,(
    ! [X0] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(resolution,[],[f176,f83])).

fof(f176,plain,(
    ! [X0] : r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[],[f145,f33])).

fof(f145,plain,(
    ! [X2,X0,X1] : r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(superposition,[],[f101,f78])).

fof(f101,plain,(
    ! [X4,X2,X0,X8,X3,X1] : r2_hidden(X8,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X8)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X8) != X6 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (11068)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (11065)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (11064)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11078)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (11075)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (11065)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (11070)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (11061)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (11083)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (11075)Refutation not found, incomplete strategy% (11075)------------------------------
% 0.20/0.52  % (11075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11073)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (11082)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (11064)Refutation not found, incomplete strategy% (11064)------------------------------
% 0.20/0.53  % (11064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11064)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11064)Memory used [KB]: 6140
% 0.20/0.53  % (11064)Time elapsed: 0.127 s
% 0.20/0.53  % (11064)------------------------------
% 0.20/0.53  % (11064)------------------------------
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f230,f114])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 0.20/0.53    inference(backward_demodulation,[],[f113,f48])).
% 0.20/0.53  % (11085)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.53  % (11075)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (11075)Memory used [KB]: 6140
% 1.39/0.53  % (11075)Time elapsed: 0.006 s
% 1.39/0.53  % (11075)------------------------------
% 1.39/0.53  % (11075)------------------------------
% 1.39/0.53  % (11062)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.53  % (11063)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.53  fof(f48,plain,(
% 1.39/0.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.39/0.53    inference(cnf_transformation,[],[f2])).
% 1.39/0.53  fof(f2,axiom,(
% 1.39/0.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.39/0.53  % (11074)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.53  fof(f113,plain,(
% 1.39/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.39/0.53    inference(forward_demodulation,[],[f99,f80])).
% 1.39/0.53  fof(f80,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f41,f77,f75,f77,f74])).
% 1.39/0.53  fof(f74,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f42,f73])).
% 1.39/0.53  fof(f73,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f51,f72])).
% 1.39/0.53  fof(f72,plain,(
% 1.39/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f66,f71])).
% 1.39/0.53  fof(f71,plain,(
% 1.39/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f68,f70])).
% 1.39/0.53  fof(f70,plain,(
% 1.39/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f67,f69])).
% 1.39/0.53  fof(f69,plain,(
% 1.39/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f9])).
% 1.39/0.53  fof(f9,axiom,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.39/0.53  fof(f67,plain,(
% 1.39/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f8])).
% 1.39/0.53  fof(f8,axiom,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.39/0.53  fof(f68,plain,(
% 1.39/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f7])).
% 1.39/0.53  fof(f7,axiom,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.39/0.53  fof(f66,plain,(
% 1.39/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f6])).
% 1.39/0.53  fof(f6,axiom,(
% 1.39/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.39/0.53  fof(f51,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f5])).
% 1.39/0.53  fof(f5,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.53  fof(f42,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f4])).
% 1.39/0.53  fof(f4,axiom,(
% 1.39/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.53  fof(f75,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f50,f74])).
% 1.39/0.53  fof(f50,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f16])).
% 1.39/0.53  fof(f16,axiom,(
% 1.39/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.39/0.53  fof(f77,plain,(
% 1.39/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f43,f74])).
% 1.39/0.53  fof(f43,plain,(
% 1.39/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f3])).
% 1.39/0.53  fof(f3,axiom,(
% 1.39/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.53  fof(f41,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f12])).
% 1.39/0.53  fof(f12,axiom,(
% 1.39/0.53    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.39/0.53  fof(f99,plain,(
% 1.39/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.39/0.53    inference(equality_resolution,[],[f82])).
% 1.39/0.53  fof(f82,plain,(
% 1.39/0.53    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f44,f77,f76,f77,f77])).
% 1.39/0.53  fof(f76,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f49,f75])).
% 1.39/0.53  fof(f49,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f1])).
% 1.39/0.53  fof(f1,axiom,(
% 1.39/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.53  fof(f44,plain,(
% 1.39/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f26])).
% 1.39/0.53  fof(f26,plain,(
% 1.39/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.39/0.53    inference(nnf_transformation,[],[f13])).
% 1.39/0.53  fof(f13,axiom,(
% 1.39/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.39/0.53  fof(f230,plain,(
% 1.39/0.53    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.39/0.53    inference(resolution,[],[f218,f39])).
% 1.39/0.53  fof(f39,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.39/0.53    inference(cnf_transformation,[],[f21])).
% 1.39/0.53  fof(f21,plain,(
% 1.39/0.53    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.39/0.53    inference(ennf_transformation,[],[f11])).
% 1.39/0.53  fof(f11,axiom,(
% 1.39/0.53    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.39/0.53  fof(f218,plain,(
% 1.39/0.53    ( ! [X0] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) )),
% 1.39/0.53    inference(backward_demodulation,[],[f181,f212])).
% 1.39/0.53  fof(f212,plain,(
% 1.39/0.53    sK0 = sK1),
% 1.39/0.53    inference(subsumption_resolution,[],[f210,f124])).
% 1.39/0.53  fof(f124,plain,(
% 1.39/0.53    ( ! [X6,X10,X8,X7,X11,X9] : (r1_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X7,X7,X7,X8,X9,X10,X6,X11))) )),
% 1.39/0.53    inference(resolution,[],[f83,f103])).
% 1.39/0.53  fof(f103,plain,(
% 1.39/0.53    ( ! [X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,k6_enumset1(X0,X0,X0,X1,X2,X3,X8,X5))) )),
% 1.39/0.53    inference(equality_resolution,[],[f102])).
% 1.39/0.53  fof(f102,plain,(
% 1.39/0.53    ( ! [X6,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X8,X5) != X6) )),
% 1.39/0.53    inference(equality_resolution,[],[f93])).
% 1.39/0.53  fof(f93,plain,(
% 1.39/0.53    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X4 != X8 | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 1.39/0.53    inference(definition_unfolding,[],[f57,f70])).
% 1.39/0.53  fof(f57,plain,(
% 1.39/0.53    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X4 != X8 | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.39/0.53    inference(cnf_transformation,[],[f32])).
% 1.39/0.53  fof(f32,plain,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | (((sK3(X0,X1,X2,X3,X4,X5,X6) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.39/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.39/0.53  fof(f31,plain,(
% 1.39/0.53    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6))) => (((sK3(X0,X1,X2,X3,X4,X5,X6) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f30,plain,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.39/0.53    inference(rectify,[],[f29])).
% 1.39/0.53  fof(f29,plain,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.39/0.53    inference(flattening,[],[f28])).
% 1.39/0.53  fof(f28,plain,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.39/0.53    inference(nnf_transformation,[],[f22])).
% 1.39/0.53  fof(f22,plain,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.39/0.53    inference(ennf_transformation,[],[f15])).
% 1.39/0.53  fof(f15,axiom,(
% 1.39/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).
% 1.39/0.53  fof(f83,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f47,f77])).
% 1.39/0.53  fof(f47,plain,(
% 1.39/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f27])).
% 1.39/0.53  fof(f27,plain,(
% 1.39/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.39/0.53    inference(nnf_transformation,[],[f10])).
% 1.39/0.53  fof(f10,axiom,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.39/0.53  fof(f210,plain,(
% 1.39/0.53    ( ! [X0] : (~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X0,sK0))) | sK0 = sK1) )),
% 1.39/0.53    inference(superposition,[],[f209,f118])).
% 1.39/0.53  fof(f118,plain,(
% 1.39/0.53    sK0 = sK2 | sK0 = sK1),
% 1.39/0.53    inference(superposition,[],[f116,f117])).
% 1.39/0.53  fof(f117,plain,(
% 1.39/0.53    k2_mcart_1(sK0) = sK2),
% 1.39/0.53    inference(superposition,[],[f36,f33])).
% 1.39/0.53  fof(f33,plain,(
% 1.39/0.53    sK0 = k4_tarski(sK1,sK2)),
% 1.39/0.53    inference(cnf_transformation,[],[f25])).
% 1.39/0.53  fof(f25,plain,(
% 1.39/0.53    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.39/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23])).
% 1.39/0.53  fof(f23,plain,(
% 1.39/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f24,plain,(
% 1.39/0.53    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f20,plain,(
% 1.39/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.39/0.53    inference(ennf_transformation,[],[f19])).
% 1.39/0.53  fof(f19,negated_conjecture,(
% 1.39/0.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.39/0.53    inference(negated_conjecture,[],[f18])).
% 1.39/0.53  fof(f18,conjecture,(
% 1.39/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.39/0.53  fof(f36,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.39/0.53    inference(cnf_transformation,[],[f17])).
% 1.39/0.53  fof(f17,axiom,(
% 1.39/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.39/0.53  fof(f116,plain,(
% 1.39/0.53    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.39/0.53    inference(backward_demodulation,[],[f34,f115])).
% 1.39/0.53  fof(f115,plain,(
% 1.39/0.53    k1_mcart_1(sK0) = sK1),
% 1.39/0.53    inference(superposition,[],[f35,f33])).
% 1.39/0.53  fof(f35,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.39/0.53    inference(cnf_transformation,[],[f17])).
% 1.39/0.53  fof(f34,plain,(
% 1.39/0.53    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.39/0.53    inference(cnf_transformation,[],[f25])).
% 1.39/0.53  fof(f209,plain,(
% 1.39/0.53    ( ! [X3] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X3,sK2)))) )),
% 1.39/0.53    inference(subsumption_resolution,[],[f203,f114])).
% 1.39/0.53  fof(f203,plain,(
% 1.39/0.53    ( ! [X3] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X3,sK2))) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) )),
% 1.39/0.53    inference(superposition,[],[f40,f141])).
% 1.39/0.53  fof(f141,plain,(
% 1.39/0.53    ( ! [X0] : (k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X0,sK2))) )),
% 1.39/0.53    inference(superposition,[],[f78,f33])).
% 1.39/0.53  fof(f78,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f38,f74,f77,f74])).
% 1.39/0.53  fof(f38,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f14])).
% 1.39/0.53  fof(f14,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.39/0.53  fof(f40,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.39/0.53    inference(cnf_transformation,[],[f21])).
% 1.39/0.53  fof(f181,plain,(
% 1.39/0.53    ( ! [X0] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) )),
% 1.39/0.53    inference(resolution,[],[f176,f83])).
% 1.39/0.53  fof(f176,plain,(
% 1.39/0.53    ( ! [X0] : (r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) )),
% 1.39/0.53    inference(superposition,[],[f145,f33])).
% 1.39/0.53  fof(f145,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 1.39/0.53    inference(superposition,[],[f101,f78])).
% 1.39/0.53  fof(f101,plain,(
% 1.39/0.53    ( ! [X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X8))) )),
% 1.39/0.53    inference(equality_resolution,[],[f100])).
% 1.39/0.53  fof(f100,plain,(
% 1.39/0.53    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X8) != X6) )),
% 1.39/0.53    inference(equality_resolution,[],[f92])).
% 1.39/0.53  fof(f92,plain,(
% 1.39/0.53    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 1.39/0.53    inference(definition_unfolding,[],[f58,f70])).
% 1.39/0.53  fof(f58,plain,(
% 1.39/0.53    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.39/0.53    inference(cnf_transformation,[],[f32])).
% 1.39/0.53  % SZS output end Proof for theBenchmark
% 1.39/0.53  % (11065)------------------------------
% 1.39/0.53  % (11065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (11065)Termination reason: Refutation
% 1.39/0.53  
% 1.39/0.53  % (11065)Memory used [KB]: 6524
% 1.39/0.53  % (11065)Time elapsed: 0.107 s
% 1.39/0.53  % (11065)------------------------------
% 1.39/0.53  % (11065)------------------------------
% 1.39/0.54  % (11059)Success in time 0.181 s
%------------------------------------------------------------------------------
