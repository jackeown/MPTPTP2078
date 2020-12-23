%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 178 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  207 ( 653 expanded)
%              Number of equality atoms :   71 ( 149 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f174,f235])).

fof(f235,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f198,f58])).

fof(f58,plain,
    ( ! [X10,X11] : X10 = X11
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> ! [X11,X10] : X10 = X11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f198,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(X0)))
    | ~ spl4_1 ),
    inference(superposition,[],[f43,f58])).

fof(f43,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f27,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f174,plain,
    ( spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f173,f57,f60])).

fof(f60,plain,
    ( spl4_2
  <=> ! [X12] : ~ r2_hidden(X12,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f173,plain,(
    ! [X4,X2,X3] :
      ( X2 = X3
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(global_subsumption,[],[f171])).

fof(f171,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | X5 = X6 ) ),
    inference(global_subsumption,[],[f169])).

fof(f169,plain,(
    ! [X6,X4,X3] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | X3 = X4 ) ),
    inference(global_subsumption,[],[f167])).

fof(f167,plain,(
    ! [X10,X8,X7] :
      ( ~ r2_hidden(X10,k1_xboole_0)
      | X7 = X8 ) ),
    inference(global_subsumption,[],[f165])).

fof(f165,plain,(
    ! [X14,X17,X15] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | X14 = X15 ) ),
    inference(subsumption_resolution,[],[f120,f122])).

fof(f122,plain,(
    ! [X12,X13,X11] :
      ( r1_xboole_0(k3_xboole_0(k1_tarski(X11),k1_tarski(X12)),X13)
      | X11 = X12 ) ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,(
    ! [X12,X13,X11] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(k1_tarski(X11),k1_tarski(X12)),X13)
      | X11 = X12 ) ),
    inference(superposition,[],[f35,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | X0 = X1 ) ),
    inference(resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f70,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),X8) ) ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f48,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f120,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | ~ r1_xboole_0(k3_xboole_0(k1_tarski(X14),k1_tarski(X15)),X16)
      | X14 = X15 ) ),
    inference(superposition,[],[f31,f94])).

fof(f150,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f147,f28])).

fof(f28,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f147,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,k1_setfam_1(k1_tarski(sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f144,f80])).

fof(f80,plain,
    ( ! [X8] : k1_xboole_0 != k1_tarski(X8)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f78,f61])).

fof(f61,plain,
    ( ! [X12] : ~ r2_hidden(X12,k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f78,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_tarski(X8)
        | r2_hidden(X8,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f33,f71])).

fof(f71,plain,
    ( ! [X9] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X9)
    | ~ spl4_2 ),
    inference(resolution,[],[f63,f61])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f144,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,k1_setfam_1(k1_tarski(sK1)))
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f43,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
        | k1_xboole_0 = X1 )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f106,f80])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (21153)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21170)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (21162)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (21144)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (21164)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (21155)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (21164)Refutation not found, incomplete strategy% (21164)------------------------------
% 0.22/0.52  % (21164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21152)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (21139)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (21152)Refutation not found, incomplete strategy% (21152)------------------------------
% 0.22/0.52  % (21152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21152)Memory used [KB]: 10618
% 0.22/0.52  % (21152)Time elapsed: 0.107 s
% 0.22/0.52  % (21152)------------------------------
% 0.22/0.52  % (21152)------------------------------
% 0.22/0.52  % (21139)Refutation not found, incomplete strategy% (21139)------------------------------
% 0.22/0.52  % (21139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21158)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (21139)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21139)Memory used [KB]: 1663
% 0.22/0.52  % (21139)Time elapsed: 0.048 s
% 0.22/0.52  % (21139)------------------------------
% 0.22/0.52  % (21139)------------------------------
% 0.22/0.52  % (21147)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21164)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21164)Memory used [KB]: 1663
% 0.22/0.52  % (21164)Time elapsed: 0.102 s
% 0.22/0.52  % (21164)------------------------------
% 0.22/0.52  % (21164)------------------------------
% 0.22/0.52  % (21158)Refutation not found, incomplete strategy% (21158)------------------------------
% 0.22/0.52  % (21158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21158)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21158)Memory used [KB]: 10618
% 0.22/0.52  % (21158)Time elapsed: 0.113 s
% 0.22/0.52  % (21158)------------------------------
% 0.22/0.52  % (21158)------------------------------
% 0.22/0.52  % (21141)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (21162)Refutation not found, incomplete strategy% (21162)------------------------------
% 0.22/0.52  % (21162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21162)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21162)Memory used [KB]: 1663
% 0.22/0.52  % (21162)Time elapsed: 0.118 s
% 0.22/0.52  % (21162)------------------------------
% 0.22/0.52  % (21162)------------------------------
% 0.22/0.53  % (21146)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (21150)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (21154)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (21144)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f150,f174,f235])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ~spl4_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    $false | ~spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f198,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X10,X11] : (X10 = X11) ) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl4_1 <=> ! [X11,X10] : X10 = X11),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X0] : (k3_xboole_0(sK0,X0) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(X0)))) ) | ~spl4_1),
% 0.22/0.53    inference(superposition,[],[f43,f58])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f27,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl4_2 | spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f173,f57,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl4_2 <=> ! [X12] : ~r2_hidden(X12,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (X2 = X3 | ~r2_hidden(X4,k1_xboole_0)) )),
% 0.22/0.53    inference(global_subsumption,[],[f171])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (~r2_hidden(X7,k1_xboole_0) | X5 = X6) )),
% 0.22/0.53    inference(global_subsumption,[],[f169])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ( ! [X6,X4,X3] : (~r2_hidden(X6,k1_xboole_0) | X3 = X4) )),
% 0.22/0.53    inference(global_subsumption,[],[f167])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X10,X8,X7] : (~r2_hidden(X10,k1_xboole_0) | X7 = X8) )),
% 0.22/0.53    inference(global_subsumption,[],[f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ( ! [X14,X17,X15] : (~r2_hidden(X17,k1_xboole_0) | X14 = X15) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f120,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ( ! [X12,X13,X11] : (r1_xboole_0(k3_xboole_0(k1_tarski(X11),k1_tarski(X12)),X13) | X11 = X12) )),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X12,X13,X11] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(k1_tarski(X11),k1_tarski(X12)),X13) | X11 = X12) )),
% 0.22/0.53    inference(superposition,[],[f35,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) | X0 = X1) )),
% 0.22/0.53    inference(resolution,[],[f70,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X6,X8,X7] : (~r1_xboole_0(X6,X7) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),X8)) )),
% 0.22/0.53    inference(resolution,[],[f63,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(resolution,[],[f48,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(resolution,[],[f30,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X14,X17,X15,X16] : (~r2_hidden(X17,k1_xboole_0) | ~r1_xboole_0(k3_xboole_0(k1_tarski(X14),k1_tarski(X15)),X16) | X14 = X15) )),
% 0.22/0.53    inference(superposition,[],[f31,f94])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ~spl4_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    $false | ~spl4_2),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f148])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | ~spl4_2),
% 0.22/0.53    inference(forward_demodulation,[],[f147,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,k1_setfam_1(k1_tarski(sK1))) | ~spl4_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f144,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X8] : (k1_xboole_0 != k1_tarski(X8)) ) | ~spl4_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f78,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X12] : (~r2_hidden(X12,k1_xboole_0)) ) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X8] : (k1_xboole_0 != k1_tarski(X8) | r2_hidden(X8,k1_xboole_0)) ) | ~spl4_2),
% 0.22/0.53    inference(superposition,[],[f33,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X9] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X9)) ) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f63,f61])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,k1_setfam_1(k1_tarski(sK1))) | k1_xboole_0 = k1_tarski(sK1) | ~spl4_2),
% 0.22/0.53    inference(superposition,[],[f43,f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1) ) | ~spl4_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f106,f80])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.53    inference(superposition,[],[f36,f28])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (21144)------------------------------
% 0.22/0.53  % (21144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21144)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (21144)Memory used [KB]: 10874
% 0.22/0.53  % (21144)Time elapsed: 0.121 s
% 0.22/0.53  % (21144)------------------------------
% 0.22/0.53  % (21144)------------------------------
% 0.22/0.53  % (21145)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (21165)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (21169)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (21135)Success in time 0.173 s
%------------------------------------------------------------------------------
