%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:27 EST 2020

% Result     : Theorem 4.92s
% Output     : Refutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :  219 (1433 expanded)
%              Number of leaves         :   36 ( 477 expanded)
%              Depth                    :   23
%              Number of atoms          :  567 (2435 expanded)
%              Number of equality atoms :  173 (1260 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f99,f1548,f2679,f2680,f2890,f2906,f3673,f4641,f4758,f5369,f6391,f6512,f6525,f6864,f6903,f6906,f6954,f9058,f9156])).

fof(f9156,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(avatar_contradiction_clause,[],[f9155])).

fof(f9155,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f9153,f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f9153,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(resolution,[],[f9017,f135])).

fof(f135,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f9017,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK0,k1_tarski(X6))
        | r2_hidden(X6,sK2) )
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(trivial_inequality_removal,[],[f8986])).

fof(f8986,plain,
    ( ! [X6] :
        ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
        | ~ r2_hidden(sK0,k1_tarski(X6))
        | r2_hidden(X6,sK2) )
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(superposition,[],[f56,f8325])).

fof(f8325,plain,
    ( ! [X4] :
        ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(X4))
        | r2_hidden(X4,sK2) )
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f8277,f1090])).

fof(f1090,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(subsumption_resolution,[],[f1076,f615])).

fof(f615,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(superposition,[],[f313,f470])).

fof(f470,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(resolution,[],[f210,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f210,plain,(
    ! [X4,X5,X3] : r1_xboole_0(k4_xboole_0(X5,X3),k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f172,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f172,plain,(
    ! [X10,X11,X9] : r1_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f71,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f313,plain,(
    ! [X14,X13] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(superposition,[],[f78,f132])).

fof(f132,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f127,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f127,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f70,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1076,plain,(
    ! [X12] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(X12,k1_xboole_0))
      | k4_xboole_0(X12,k1_xboole_0) = X12 ) ),
    inference(superposition,[],[f115,f612])).

fof(f612,plain,(
    ! [X13] : k1_xboole_0 = k3_xboole_0(X13,k1_xboole_0) ),
    inference(superposition,[],[f132,f470])).

fof(f115,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(superposition,[],[f68,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f8277,plain,
    ( ! [X4] :
        ( k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(X4))
        | r2_hidden(X4,sK2) )
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(superposition,[],[f8238,f597])).

fof(f597,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X2),X3)
      | r2_hidden(X2,X3) ) ),
    inference(backward_demodulation,[],[f155,f470])).

fof(f155,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k1_tarski(X2),X3) = k4_xboole_0(k1_tarski(X2),k1_tarski(X2))
      | r2_hidden(X2,X3) ) ),
    inference(superposition,[],[f70,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f8238,plain,
    ( ! [X3] : k4_xboole_0(k2_tarski(sK0,sK1),X3) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(X3,sK2))
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f2921,f7906])).

fof(f7906,plain,
    ( ! [X22] : k2_xboole_0(X22,k1_xboole_0) = X22
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f7905,f3686])).

fof(f3686,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f3685,f612])).

fof(f3685,plain,
    ( ! [X2] : k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),X2) = X2
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f3675,f1090])).

fof(f3675,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))
    | ~ spl5_57 ),
    inference(superposition,[],[f170,f3223])).

fof(f3223,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f3221])).

fof(f3221,plain,
    ( spl5_57
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f170,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,X4) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X5),k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f68,f67])).

fof(f7905,plain,
    ( ! [X22] : k2_xboole_0(k1_xboole_0,X22) = k2_xboole_0(k2_xboole_0(k1_xboole_0,X22),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f7882,f612])).

fof(f7882,plain,
    ( ! [X22] : k2_xboole_0(k1_xboole_0,X22) = k2_xboole_0(k2_xboole_0(k1_xboole_0,X22),k3_xboole_0(k5_xboole_0(k1_xboole_0,X22),k1_xboole_0))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(superposition,[],[f201,f7856])).

fof(f7856,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f7118,f7433])).

fof(f7433,plain,
    ( ! [X12] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X12,sK2))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f7409,f470])).

fof(f7409,plain,
    ( ! [X12] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X12,sK2))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(superposition,[],[f70,f7340])).

fof(f7340,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f6881,f6959])).

fof(f6959,plain,
    ( ! [X6] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f6958,f470])).

fof(f6958,plain,
    ( ! [X6] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f6957,f612])).

fof(f6957,plain,
    ( ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k1_xboole_0))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f6928,f1390])).

fof(f1390,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1388,plain,
    ( spl5_15
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f6928,plain,
    ( ! [X6] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k4_xboole_0(k1_xboole_0,sK2))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl5_61 ),
    inference(superposition,[],[f236,f3333])).

fof(f3333,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f3331])).

fof(f3331,plain,
    ( spl5_61
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f236,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k3_xboole_0(X5,k4_xboole_0(X3,X4))) = k2_xboole_0(k4_xboole_0(X3,X5),k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f66,f70])).

fof(f66,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f6881,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)
    | ~ spl5_15 ),
    inference(superposition,[],[f66,f1390])).

fof(f7118,plain,
    ( ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f7117,f1090])).

fof(f7117,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f7081,f70])).

fof(f7081,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2)))
    | ~ spl5_15 ),
    inference(superposition,[],[f164,f6881])).

fof(f164,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5) ),
    inference(superposition,[],[f67,f70])).

fof(f201,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f199,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f199,plain,(
    ! [X0,X1] : k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f2921,plain,
    ( ! [X3] : k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(X3,sK2)) = k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),X3),k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f66,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f9058,plain,
    ( spl5_3
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f9029,f3331,f3221,f1388,f86,f94])).

fof(f94,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f9029,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(resolution,[],[f9016,f135])).

fof(f9016,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK1,k1_tarski(X7))
        | r2_hidden(X7,sK2) )
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(trivial_inequality_removal,[],[f8987])).

fof(f8987,plain,
    ( ! [X7] :
        ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
        | ~ r2_hidden(sK1,k1_tarski(X7))
        | r2_hidden(X7,sK2) )
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(superposition,[],[f57,f8325])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6954,plain,
    ( spl5_80
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f6953,f3331,f3221,f4161])).

fof(f4161,plain,
    ( spl5_80
  <=> sK2 = k2_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f6953,plain,
    ( sK2 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_57
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f6952,f3686])).

fof(f6952,plain,
    ( k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(k2_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f6926,f612])).

fof(f6926,plain,
    ( k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(k2_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0))
    | ~ spl5_61 ),
    inference(superposition,[],[f201,f3333])).

fof(f6906,plain,
    ( spl5_62
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f6900,f1388,f3336])).

fof(f3336,plain,
    ( spl5_62
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f6900,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_15 ),
    inference(superposition,[],[f344,f1390])).

fof(f344,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f128,f132])).

fof(f128,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f68,f70])).

fof(f6903,plain,
    ( spl5_61
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f6902,f1388,f3331])).

fof(f6902,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f6884,f470])).

fof(f6884,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_15 ),
    inference(superposition,[],[f70,f1390])).

fof(f6864,plain,
    ( spl5_15
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f6842,f4030,f1388])).

fof(f4030,plain,
    ( spl5_72
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f6842,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_72 ),
    inference(forward_demodulation,[],[f6841,f612])).

fof(f6841,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k3_xboole_0(k4_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl5_72 ),
    inference(forward_demodulation,[],[f6813,f1090])).

fof(f6813,plain,
    ( k3_xboole_0(k4_xboole_0(k1_xboole_0,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl5_72 ),
    inference(superposition,[],[f169,f4032])).

fof(f4032,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f4030])).

fof(f169,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f70,f67])).

fof(f6525,plain,
    ( spl5_72
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f6524,f3325,f4030])).

fof(f3325,plain,
    ( spl5_60
  <=> k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f6524,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f6513,f470])).

fof(f6513,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_60 ),
    inference(superposition,[],[f175,f3327])).

fof(f3327,plain,
    ( k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f3325])).

fof(f175,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f163,f67])).

fof(f163,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f67,f69])).

fof(f6512,plain,(
    spl5_60 ),
    inference(avatar_contradiction_clause,[],[f6511])).

fof(f6511,plain,
    ( $false
    | spl5_60 ),
    inference(subsumption_resolution,[],[f6509,f78])).

fof(f6509,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | spl5_60 ),
    inference(trivial_inequality_removal,[],[f6508])).

fof(f6508,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | spl5_60 ),
    inference(superposition,[],[f3326,f79])).

fof(f3326,plain,
    ( k1_xboole_0 != k2_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | spl5_60 ),
    inference(avatar_component_clause,[],[f3325])).

fof(f6391,plain,
    ( spl5_19
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f5898,f1503,f1462])).

fof(f1462,plain,
    ( spl5_19
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1503,plain,
    ( spl5_26
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f5898,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f5872,f470])).

fof(f5872,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)))
    | ~ spl5_26 ),
    inference(superposition,[],[f68,f1505])).

fof(f1505,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f1503])).

fof(f5369,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f5368,f3331,f1388,f86,f1462])).

fof(f5368,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f5367,f1090])).

fof(f5367,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f5337,f4471])).

fof(f4471,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3619,f3787])).

fof(f3787,plain,
    ( ! [X13] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X13,sK2))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3767,f470])).

fof(f3767,plain,
    ( ! [X13] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X13,sK2))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(superposition,[],[f70,f3703])).

fof(f3703,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f3304,f3440])).

fof(f3440,plain,
    ( ! [X6] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3439,f470])).

fof(f3439,plain,
    ( ! [X6] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3438,f612])).

fof(f3438,plain,
    ( ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k1_xboole_0))
    | ~ spl5_15
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3397,f1390])).

fof(f3397,plain,
    ( ! [X6] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k4_xboole_0(k1_xboole_0,sK2))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl5_61 ),
    inference(superposition,[],[f236,f3333])).

fof(f3304,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)
    | ~ spl5_15 ),
    inference(superposition,[],[f66,f1390])).

fof(f3619,plain,
    ( ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f3618,f1090])).

fof(f3618,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f3588,f70])).

fof(f3588,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2)))
    | ~ spl5_15 ),
    inference(superposition,[],[f164,f3304])).

fof(f5337,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f2921,f1090])).

fof(f4758,plain,
    ( spl5_26
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f4722,f1358,f1503])).

fof(f1358,plain,
    ( spl5_12
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f4722,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))
    | ~ spl5_12 ),
    inference(superposition,[],[f131,f1360])).

fof(f1360,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f1358])).

fof(f131,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f126,f70])).

fof(f126,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f70,f69])).

fof(f4641,plain,
    ( spl5_1
    | ~ spl5_30
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f4640,f4161,f1545,f86])).

fof(f1545,plain,
    ( spl5_30
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f4640,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_30
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f1547,f4163])).

fof(f4163,plain,
    ( sK2 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f4161])).

fof(f1547,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f3673,plain,
    ( spl5_57
    | ~ spl5_61
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f3672,f3336,f3331,f3221])).

fof(f3672,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_61
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f3338,f3333])).

fof(f3338,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f3336])).

fof(f2906,plain,
    ( ~ spl5_3
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f2905])).

fof(f2905,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f2896,f71])).

fof(f2896,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)
    | ~ spl5_3
    | ~ spl5_48 ),
    inference(resolution,[],[f2643,f1392])).

fof(f1392,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f95,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f2643,plain,
    ( r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f2641])).

fof(f2641,plain,
    ( spl5_48
  <=> r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f2890,plain,
    ( ~ spl5_2
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f2889])).

fof(f2889,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f2882,f71])).

fof(f2882,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)
    | ~ spl5_2
    | ~ spl5_37 ),
    inference(resolution,[],[f2139,f1526])).

fof(f1526,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f91,f63])).

fof(f91,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f2139,plain,
    ( r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f2138])).

fof(f2138,plain,
    ( spl5_37
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f2680,plain,
    ( spl5_37
    | spl5_48
    | ~ spl5_19
    | spl5_11 ),
    inference(avatar_split_clause,[],[f2588,f1352,f1462,f2641,f2138])).

fof(f1352,plain,
    ( spl5_11
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f2588,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl5_11 ),
    inference(superposition,[],[f1353,f261])).

fof(f261,plain,(
    ! [X6,X8,X7] :
      ( k2_tarski(X6,X7) = k3_xboole_0(k2_tarski(X6,X7),X8)
      | r2_hidden(X7,k4_xboole_0(k2_tarski(X6,X7),X8))
      | r2_hidden(X6,k4_xboole_0(k2_tarski(X6,X7),X8)) ) ),
    inference(superposition,[],[f58,f70])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1353,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),sK2),k1_xboole_0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f2679,plain,
    ( spl5_37
    | spl5_48
    | spl5_12 ),
    inference(avatar_split_clause,[],[f2632,f1358,f2641,f2138])).

fof(f2632,plain,
    ( r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl5_12 ),
    inference(trivial_inequality_removal,[],[f2589])).

fof(f2589,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl5_12 ),
    inference(superposition,[],[f1359,f261])).

fof(f1359,plain,
    ( k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f1358])).

fof(f1548,plain,
    ( spl5_30
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1543,f1352,f1545])).

fof(f1543,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1532,f470])).

fof(f1532,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_11 ),
    inference(superposition,[],[f175,f1354])).

fof(f1354,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f99,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f47,f90,f86])).

fof(f47,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f98,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f48,f94,f86])).

fof(f48,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f49,f94,f90,f86])).

fof(f49,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (31902)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % (31894)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (31910)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (31890)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (31893)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (31892)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (31905)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (31908)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (31909)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (31889)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (31889)Refutation not found, incomplete strategy% (31889)------------------------------
% 0.20/0.52  % (31889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31889)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31889)Memory used [KB]: 1663
% 0.20/0.52  % (31889)Time elapsed: 0.102 s
% 0.20/0.52  % (31889)------------------------------
% 0.20/0.52  % (31889)------------------------------
% 0.20/0.52  % (31911)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (31903)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (31897)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (31891)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (31915)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (31896)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (31917)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (31907)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (31895)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (31906)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (31914)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (31914)Refutation not found, incomplete strategy% (31914)------------------------------
% 0.20/0.54  % (31914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31901)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (31913)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (31916)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (31888)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (31900)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (31898)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (31899)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (31898)Refutation not found, incomplete strategy% (31898)------------------------------
% 0.20/0.54  % (31898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31898)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31898)Memory used [KB]: 10746
% 0.20/0.54  % (31898)Time elapsed: 0.150 s
% 0.20/0.54  % (31898)------------------------------
% 0.20/0.54  % (31898)------------------------------
% 0.20/0.55  % (31914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31914)Memory used [KB]: 6268
% 0.20/0.55  % (31914)Time elapsed: 0.140 s
% 0.20/0.55  % (31914)------------------------------
% 0.20/0.55  % (31914)------------------------------
% 0.20/0.55  % (31916)Refutation not found, incomplete strategy% (31916)------------------------------
% 0.20/0.55  % (31916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31916)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31916)Memory used [KB]: 10746
% 0.20/0.55  % (31916)Time elapsed: 0.152 s
% 0.20/0.55  % (31916)------------------------------
% 0.20/0.55  % (31916)------------------------------
% 0.20/0.55  % (31917)Refutation not found, incomplete strategy% (31917)------------------------------
% 0.20/0.55  % (31917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31917)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31917)Memory used [KB]: 1663
% 0.20/0.55  % (31917)Time elapsed: 0.003 s
% 0.20/0.55  % (31917)------------------------------
% 0.20/0.55  % (31917)------------------------------
% 0.20/0.55  % (31904)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (31904)Refutation not found, incomplete strategy% (31904)------------------------------
% 0.20/0.55  % (31904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31904)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31904)Memory used [KB]: 10618
% 0.20/0.55  % (31904)Time elapsed: 0.158 s
% 0.20/0.55  % (31904)------------------------------
% 0.20/0.55  % (31904)------------------------------
% 0.20/0.56  % (31912)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.08/0.67  % (31891)Refutation not found, incomplete strategy% (31891)------------------------------
% 2.08/0.67  % (31891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.67  % (31923)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.08/0.68  % (31924)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.08/0.68  % (31927)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.08/0.68  % (31925)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.08/0.68  % (31925)Refutation not found, incomplete strategy% (31925)------------------------------
% 2.08/0.68  % (31925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (31925)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.68  
% 2.08/0.68  % (31925)Memory used [KB]: 6140
% 2.08/0.68  % (31925)Time elapsed: 0.114 s
% 2.08/0.68  % (31925)------------------------------
% 2.08/0.68  % (31925)------------------------------
% 2.08/0.68  % (31891)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.68  
% 2.08/0.68  % (31891)Memory used [KB]: 6140
% 2.08/0.68  % (31891)Time elapsed: 0.267 s
% 2.08/0.68  % (31891)------------------------------
% 2.08/0.68  % (31891)------------------------------
% 2.08/0.69  % (31928)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.08/0.70  % (31926)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.33/0.80  % (31912)Time limit reached!
% 3.33/0.80  % (31912)------------------------------
% 3.33/0.80  % (31912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.81  % (31912)Termination reason: Time limit
% 3.33/0.81  % (31912)Termination phase: Saturation
% 3.33/0.81  
% 3.33/0.81  % (31912)Memory used [KB]: 12920
% 3.33/0.81  % (31912)Time elapsed: 0.400 s
% 3.33/0.81  % (31912)------------------------------
% 3.33/0.81  % (31912)------------------------------
% 3.33/0.81  % (31890)Time limit reached!
% 3.33/0.81  % (31890)------------------------------
% 3.33/0.81  % (31890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.82  % (31890)Termination reason: Time limit
% 3.33/0.82  
% 3.33/0.82  % (31890)Memory used [KB]: 6780
% 3.33/0.82  % (31890)Time elapsed: 0.418 s
% 3.33/0.82  % (31890)------------------------------
% 3.33/0.82  % (31890)------------------------------
% 3.33/0.82  % (31960)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.33/0.83  % (31959)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.17/0.92  % (31902)Time limit reached!
% 4.17/0.92  % (31902)------------------------------
% 4.17/0.92  % (31902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.92  % (31902)Termination reason: Time limit
% 4.17/0.92  
% 4.17/0.92  % (31902)Memory used [KB]: 5117
% 4.17/0.92  % (31902)Time elapsed: 0.523 s
% 4.17/0.92  % (31902)------------------------------
% 4.17/0.92  % (31902)------------------------------
% 4.27/0.92  % (31894)Time limit reached!
% 4.27/0.92  % (31894)------------------------------
% 4.27/0.92  % (31894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.92  % (31894)Termination reason: Time limit
% 4.27/0.92  
% 4.27/0.92  % (31894)Memory used [KB]: 16119
% 4.27/0.92  % (31894)Time elapsed: 0.526 s
% 4.27/0.92  % (31894)------------------------------
% 4.27/0.92  % (31894)------------------------------
% 4.27/0.93  % (32015)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.27/0.95  % (32024)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.92/1.02  % (31909)Refutation found. Thanks to Tanya!
% 4.92/1.02  % SZS status Theorem for theBenchmark
% 4.92/1.02  % SZS output start Proof for theBenchmark
% 4.92/1.02  fof(f9157,plain,(
% 4.92/1.02    $false),
% 4.92/1.02    inference(avatar_sat_refutation,[],[f97,f98,f99,f1548,f2679,f2680,f2890,f2906,f3673,f4641,f4758,f5369,f6391,f6512,f6525,f6864,f6903,f6906,f6954,f9058,f9156])).
% 4.92/1.02  fof(f9156,plain,(
% 4.92/1.02    ~spl5_1 | spl5_2 | ~spl5_15 | ~spl5_57 | ~spl5_61),
% 4.92/1.02    inference(avatar_contradiction_clause,[],[f9155])).
% 4.92/1.02  fof(f9155,plain,(
% 4.92/1.02    $false | (~spl5_1 | spl5_2 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(subsumption_resolution,[],[f9153,f92])).
% 4.92/1.02  fof(f92,plain,(
% 4.92/1.02    ~r2_hidden(sK0,sK2) | spl5_2),
% 4.92/1.02    inference(avatar_component_clause,[],[f90])).
% 4.92/1.02  fof(f90,plain,(
% 4.92/1.02    spl5_2 <=> r2_hidden(sK0,sK2)),
% 4.92/1.02    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 4.92/1.02  fof(f9153,plain,(
% 4.92/1.02    r2_hidden(sK0,sK2) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(resolution,[],[f9017,f135])).
% 4.92/1.02  fof(f135,plain,(
% 4.92/1.02    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 4.92/1.02    inference(resolution,[],[f53,f83])).
% 4.92/1.02  fof(f83,plain,(
% 4.92/1.02    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 4.92/1.02    inference(equality_resolution,[],[f82])).
% 4.92/1.02  fof(f82,plain,(
% 4.92/1.02    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X0 != X2) )),
% 4.92/1.02    inference(equality_resolution,[],[f52])).
% 4.92/1.02  fof(f52,plain,(
% 4.92/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 4.92/1.02    inference(cnf_transformation,[],[f37])).
% 4.92/1.02  fof(f37,plain,(
% 4.92/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 4.92/1.02    inference(flattening,[],[f36])).
% 4.92/1.02  fof(f36,plain,(
% 4.92/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 4.92/1.02    inference(nnf_transformation,[],[f20])).
% 4.92/1.02  fof(f20,axiom,(
% 4.92/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 4.92/1.02  fof(f53,plain,(
% 4.92/1.02    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 4.92/1.02    inference(cnf_transformation,[],[f39])).
% 4.92/1.02  fof(f39,plain,(
% 4.92/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 4.92/1.02    inference(flattening,[],[f38])).
% 4.92/1.02  fof(f38,plain,(
% 4.92/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 4.92/1.02    inference(nnf_transformation,[],[f19])).
% 4.92/1.02  fof(f19,axiom,(
% 4.92/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 4.92/1.02  fof(f9017,plain,(
% 4.92/1.02    ( ! [X6] : (~r2_hidden(sK0,k1_tarski(X6)) | r2_hidden(X6,sK2)) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(trivial_inequality_removal,[],[f8986])).
% 4.92/1.02  fof(f8986,plain,(
% 4.92/1.02    ( ! [X6] : (k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r2_hidden(sK0,k1_tarski(X6)) | r2_hidden(X6,sK2)) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(superposition,[],[f56,f8325])).
% 4.92/1.02  fof(f8325,plain,(
% 4.92/1.02    ( ! [X4] : (k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(X4)) | r2_hidden(X4,sK2)) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f8277,f1090])).
% 4.92/1.02  fof(f1090,plain,(
% 4.92/1.02    ( ! [X12] : (k4_xboole_0(X12,k1_xboole_0) = X12) )),
% 4.92/1.02    inference(subsumption_resolution,[],[f1076,f615])).
% 4.92/1.02  fof(f615,plain,(
% 4.92/1.02    ( ! [X18] : (r1_tarski(k1_xboole_0,X18)) )),
% 4.92/1.02    inference(superposition,[],[f313,f470])).
% 4.92/1.02  fof(f470,plain,(
% 4.92/1.02    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 4.92/1.02    inference(resolution,[],[f210,f74])).
% 4.92/1.02  fof(f74,plain,(
% 4.92/1.02    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 4.92/1.02    inference(cnf_transformation,[],[f29])).
% 4.92/1.02  fof(f29,plain,(
% 4.92/1.02    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 4.92/1.02    inference(ennf_transformation,[],[f12])).
% 4.92/1.02  fof(f12,axiom,(
% 4.92/1.02    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 4.92/1.02  fof(f210,plain,(
% 4.92/1.02    ( ! [X4,X5,X3] : (r1_xboole_0(k4_xboole_0(X5,X3),k4_xboole_0(X3,X4))) )),
% 4.92/1.02    inference(superposition,[],[f172,f68])).
% 4.92/1.02  fof(f68,plain,(
% 4.92/1.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 4.92/1.02    inference(cnf_transformation,[],[f11])).
% 4.92/1.02  fof(f11,axiom,(
% 4.92/1.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 4.92/1.02  fof(f172,plain,(
% 4.92/1.02    ( ! [X10,X11,X9] : (r1_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X11)) )),
% 4.92/1.02    inference(superposition,[],[f71,f67])).
% 4.92/1.02  fof(f67,plain,(
% 4.92/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.92/1.02    inference(cnf_transformation,[],[f8])).
% 4.92/1.02  fof(f8,axiom,(
% 4.92/1.02    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.92/1.02  fof(f71,plain,(
% 4.92/1.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.92/1.02    inference(cnf_transformation,[],[f13])).
% 4.92/1.02  fof(f13,axiom,(
% 4.92/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.92/1.02  fof(f313,plain,(
% 4.92/1.02    ( ! [X14,X13] : (r1_tarski(k4_xboole_0(X13,X14),X13)) )),
% 4.92/1.02    inference(superposition,[],[f78,f132])).
% 4.92/1.02  fof(f132,plain,(
% 4.92/1.02    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 4.92/1.02    inference(forward_demodulation,[],[f127,f69])).
% 4.92/1.02  fof(f69,plain,(
% 4.92/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.92/1.02    inference(cnf_transformation,[],[f9])).
% 4.92/1.02  fof(f9,axiom,(
% 4.92/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.92/1.02  fof(f127,plain,(
% 4.92/1.02    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 4.92/1.02    inference(superposition,[],[f70,f70])).
% 4.92/1.02  fof(f70,plain,(
% 4.92/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.92/1.02    inference(cnf_transformation,[],[f10])).
% 4.92/1.02  fof(f10,axiom,(
% 4.92/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.92/1.02  fof(f78,plain,(
% 4.92/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.92/1.02    inference(cnf_transformation,[],[f7])).
% 4.92/1.02  fof(f7,axiom,(
% 4.92/1.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.92/1.02  fof(f1076,plain,(
% 4.92/1.02    ( ! [X12] : (~r1_tarski(k1_xboole_0,k4_xboole_0(X12,k1_xboole_0)) | k4_xboole_0(X12,k1_xboole_0) = X12) )),
% 4.92/1.02    inference(superposition,[],[f115,f612])).
% 4.92/1.02  fof(f612,plain,(
% 4.92/1.02    ( ! [X13] : (k1_xboole_0 = k3_xboole_0(X13,k1_xboole_0)) )),
% 4.92/1.02    inference(superposition,[],[f132,f470])).
% 4.92/1.02  fof(f115,plain,(
% 4.92/1.02    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 4.92/1.02    inference(superposition,[],[f68,f79])).
% 4.92/1.02  fof(f79,plain,(
% 4.92/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.92/1.02    inference(cnf_transformation,[],[f31])).
% 4.92/1.02  fof(f31,plain,(
% 4.92/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.92/1.02    inference(ennf_transformation,[],[f6])).
% 4.92/1.02  fof(f6,axiom,(
% 4.92/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.92/1.02  fof(f8277,plain,(
% 4.92/1.02    ( ! [X4] : (k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(X4)) | r2_hidden(X4,sK2)) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(superposition,[],[f8238,f597])).
% 4.92/1.02  fof(f597,plain,(
% 4.92/1.02    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k1_tarski(X2),X3) | r2_hidden(X2,X3)) )),
% 4.92/1.02    inference(backward_demodulation,[],[f155,f470])).
% 4.92/1.02  fof(f155,plain,(
% 4.92/1.02    ( ! [X2,X3] : (k3_xboole_0(k1_tarski(X2),X3) = k4_xboole_0(k1_tarski(X2),k1_tarski(X2)) | r2_hidden(X2,X3)) )),
% 4.92/1.02    inference(superposition,[],[f70,f60])).
% 4.92/1.02  fof(f60,plain,(
% 4.92/1.02    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 4.92/1.02    inference(cnf_transformation,[],[f42])).
% 4.92/1.02  fof(f42,plain,(
% 4.92/1.02    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 4.92/1.02    inference(nnf_transformation,[],[f18])).
% 4.92/1.02  fof(f18,axiom,(
% 4.92/1.02    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 4.92/1.02  fof(f8238,plain,(
% 4.92/1.02    ( ! [X3] : (k4_xboole_0(k2_tarski(sK0,sK1),X3) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(X3,sK2))) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(backward_demodulation,[],[f2921,f7906])).
% 4.92/1.02  fof(f7906,plain,(
% 4.92/1.02    ( ! [X22] : (k2_xboole_0(X22,k1_xboole_0) = X22) ) | (~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f7905,f3686])).
% 4.92/1.02  fof(f3686,plain,(
% 4.92/1.02    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) ) | ~spl5_57),
% 4.92/1.02    inference(forward_demodulation,[],[f3685,f612])).
% 4.92/1.02  fof(f3685,plain,(
% 4.92/1.02    ( ! [X2] : (k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),X2) = X2) ) | ~spl5_57),
% 4.92/1.02    inference(forward_demodulation,[],[f3675,f1090])).
% 4.92/1.02  fof(f3675,plain,(
% 4.92/1.02    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))) ) | ~spl5_57),
% 4.92/1.02    inference(superposition,[],[f170,f3223])).
% 4.92/1.02  fof(f3223,plain,(
% 4.92/1.02    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_57),
% 4.92/1.02    inference(avatar_component_clause,[],[f3221])).
% 4.92/1.02  fof(f3221,plain,(
% 4.92/1.02    spl5_57 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.92/1.02    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 4.92/1.02  fof(f170,plain,(
% 4.92/1.02    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X4) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X5),k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 4.92/1.02    inference(superposition,[],[f68,f67])).
% 4.92/1.02  fof(f7905,plain,(
% 4.92/1.02    ( ! [X22] : (k2_xboole_0(k1_xboole_0,X22) = k2_xboole_0(k2_xboole_0(k1_xboole_0,X22),k1_xboole_0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f7882,f612])).
% 4.92/1.02  fof(f7882,plain,(
% 4.92/1.02    ( ! [X22] : (k2_xboole_0(k1_xboole_0,X22) = k2_xboole_0(k2_xboole_0(k1_xboole_0,X22),k3_xboole_0(k5_xboole_0(k1_xboole_0,X22),k1_xboole_0))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(superposition,[],[f201,f7856])).
% 4.92/1.02  fof(f7856,plain,(
% 4.92/1.02    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f7118,f7433])).
% 4.92/1.02  fof(f7433,plain,(
% 4.92/1.02    ( ! [X12] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X12,sK2))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f7409,f470])).
% 4.92/1.02  fof(f7409,plain,(
% 4.92/1.02    ( ! [X12] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X12,sK2))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(superposition,[],[f70,f7340])).
% 4.92/1.02  fof(f7340,plain,(
% 4.92/1.02    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(backward_demodulation,[],[f6881,f6959])).
% 4.92/1.02  fof(f6959,plain,(
% 4.92/1.02    ( ! [X6] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f6958,f470])).
% 4.92/1.02  fof(f6958,plain,(
% 4.92/1.02    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f6957,f612])).
% 4.92/1.02  fof(f6957,plain,(
% 4.92/1.02    ( ! [X6] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k1_xboole_0))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.02    inference(forward_demodulation,[],[f6928,f1390])).
% 4.92/1.02  fof(f1390,plain,(
% 4.92/1.02    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl5_15),
% 4.92/1.02    inference(avatar_component_clause,[],[f1388])).
% 4.92/1.02  fof(f1388,plain,(
% 4.92/1.02    spl5_15 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 4.92/1.02    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 4.92/1.02  fof(f6928,plain,(
% 4.92/1.02    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k4_xboole_0(k1_xboole_0,sK2))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)) ) | ~spl5_61),
% 4.92/1.02    inference(superposition,[],[f236,f3333])).
% 4.92/1.02  fof(f3333,plain,(
% 4.92/1.02    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl5_61),
% 4.92/1.02    inference(avatar_component_clause,[],[f3331])).
% 4.92/1.02  fof(f3331,plain,(
% 4.92/1.02    spl5_61 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 4.92/1.02    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 4.92/1.02  fof(f236,plain,(
% 4.92/1.02    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k3_xboole_0(X5,k4_xboole_0(X3,X4))) = k2_xboole_0(k4_xboole_0(X3,X5),k3_xboole_0(X3,X4))) )),
% 4.92/1.02    inference(superposition,[],[f66,f70])).
% 4.92/1.02  fof(f66,plain,(
% 4.92/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 4.92/1.02    inference(cnf_transformation,[],[f5])).
% 4.92/1.02  fof(f5,axiom,(
% 4.92/1.02    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 4.92/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 4.92/1.02  fof(f6881,plain,(
% 4.92/1.02    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ) | ~spl5_15),
% 4.92/1.02    inference(superposition,[],[f66,f1390])).
% 4.92/1.02  fof(f7118,plain,(
% 4.92/1.02    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))) ) | ~spl5_15),
% 4.92/1.02    inference(forward_demodulation,[],[f7117,f1090])).
% 4.92/1.03  fof(f7117,plain,(
% 4.92/1.03    ( ! [X0] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))) ) | ~spl5_15),
% 4.92/1.03    inference(forward_demodulation,[],[f7081,f70])).
% 4.92/1.03  fof(f7081,plain,(
% 4.92/1.03    ( ! [X0] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2)))) ) | ~spl5_15),
% 4.92/1.03    inference(superposition,[],[f164,f6881])).
% 4.92/1.03  fof(f164,plain,(
% 4.92/1.03    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5)) )),
% 4.92/1.03    inference(superposition,[],[f67,f70])).
% 4.92/1.03  fof(f201,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 4.92/1.03    inference(forward_demodulation,[],[f199,f76])).
% 4.92/1.03  fof(f76,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.92/1.03    inference(cnf_transformation,[],[f14])).
% 4.92/1.03  fof(f14,axiom,(
% 4.92/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 4.92/1.03  fof(f199,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 4.92/1.03    inference(superposition,[],[f76,f77])).
% 4.92/1.03  fof(f77,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.92/1.03    inference(cnf_transformation,[],[f15])).
% 4.92/1.03  fof(f15,axiom,(
% 4.92/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 4.92/1.03  fof(f2921,plain,(
% 4.92/1.03    ( ! [X3] : (k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(X3,sK2)) = k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),X3),k1_xboole_0)) ) | ~spl5_1),
% 4.92/1.03    inference(superposition,[],[f66,f87])).
% 4.92/1.03  fof(f87,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 4.92/1.03    inference(avatar_component_clause,[],[f86])).
% 4.92/1.03  fof(f86,plain,(
% 4.92/1.03    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 4.92/1.03  fof(f56,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 4.92/1.03    inference(cnf_transformation,[],[f41])).
% 4.92/1.03  fof(f41,plain,(
% 4.92/1.03    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.92/1.03    inference(flattening,[],[f40])).
% 4.92/1.03  fof(f40,plain,(
% 4.92/1.03    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.92/1.03    inference(nnf_transformation,[],[f21])).
% 4.92/1.03  fof(f21,axiom,(
% 4.92/1.03    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 4.92/1.03  fof(f9058,plain,(
% 4.92/1.03    spl5_3 | ~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61),
% 4.92/1.03    inference(avatar_split_clause,[],[f9029,f3331,f3221,f1388,f86,f94])).
% 4.92/1.03  fof(f94,plain,(
% 4.92/1.03    spl5_3 <=> r2_hidden(sK1,sK2)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 4.92/1.03  fof(f9029,plain,(
% 4.92/1.03    r2_hidden(sK1,sK2) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.03    inference(resolution,[],[f9016,f135])).
% 4.92/1.03  fof(f9016,plain,(
% 4.92/1.03    ( ! [X7] : (~r2_hidden(sK1,k1_tarski(X7)) | r2_hidden(X7,sK2)) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.03    inference(trivial_inequality_removal,[],[f8987])).
% 4.92/1.03  fof(f8987,plain,(
% 4.92/1.03    ( ! [X7] : (k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r2_hidden(sK1,k1_tarski(X7)) | r2_hidden(X7,sK2)) ) | (~spl5_1 | ~spl5_15 | ~spl5_57 | ~spl5_61)),
% 4.92/1.03    inference(superposition,[],[f57,f8325])).
% 4.92/1.03  fof(f57,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 4.92/1.03    inference(cnf_transformation,[],[f41])).
% 4.92/1.03  fof(f6954,plain,(
% 4.92/1.03    spl5_80 | ~spl5_57 | ~spl5_61),
% 4.92/1.03    inference(avatar_split_clause,[],[f6953,f3331,f3221,f4161])).
% 4.92/1.03  fof(f4161,plain,(
% 4.92/1.03    spl5_80 <=> sK2 = k2_xboole_0(sK2,k1_xboole_0)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 4.92/1.03  fof(f6953,plain,(
% 4.92/1.03    sK2 = k2_xboole_0(sK2,k1_xboole_0) | (~spl5_57 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f6952,f3686])).
% 4.92/1.03  fof(f6952,plain,(
% 4.92/1.03    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(k2_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | ~spl5_61),
% 4.92/1.03    inference(forward_demodulation,[],[f6926,f612])).
% 4.92/1.03  fof(f6926,plain,(
% 4.92/1.03    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(k2_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0)) | ~spl5_61),
% 4.92/1.03    inference(superposition,[],[f201,f3333])).
% 4.92/1.03  fof(f6906,plain,(
% 4.92/1.03    spl5_62 | ~spl5_15),
% 4.92/1.03    inference(avatar_split_clause,[],[f6900,f1388,f3336])).
% 4.92/1.03  fof(f3336,plain,(
% 4.92/1.03    spl5_62 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2))),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 4.92/1.03  fof(f6900,plain,(
% 4.92/1.03    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) | ~spl5_15),
% 4.92/1.03    inference(superposition,[],[f344,f1390])).
% 4.92/1.03  fof(f344,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 4.92/1.03    inference(forward_demodulation,[],[f128,f132])).
% 4.92/1.03  fof(f128,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) )),
% 4.92/1.03    inference(superposition,[],[f68,f70])).
% 4.92/1.03  fof(f6903,plain,(
% 4.92/1.03    spl5_61 | ~spl5_15),
% 4.92/1.03    inference(avatar_split_clause,[],[f6902,f1388,f3331])).
% 4.92/1.03  fof(f6902,plain,(
% 4.92/1.03    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl5_15),
% 4.92/1.03    inference(forward_demodulation,[],[f6884,f470])).
% 4.92/1.03  fof(f6884,plain,(
% 4.92/1.03    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2) | ~spl5_15),
% 4.92/1.03    inference(superposition,[],[f70,f1390])).
% 4.92/1.03  fof(f6864,plain,(
% 4.92/1.03    spl5_15 | ~spl5_72),
% 4.92/1.03    inference(avatar_split_clause,[],[f6842,f4030,f1388])).
% 4.92/1.03  fof(f4030,plain,(
% 4.92/1.03    spl5_72 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0))),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 4.92/1.03  fof(f6842,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl5_72),
% 4.92/1.03    inference(forward_demodulation,[],[f6841,f612])).
% 4.92/1.03  fof(f6841,plain,(
% 4.92/1.03    k4_xboole_0(k1_xboole_0,sK2) = k3_xboole_0(k4_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | ~spl5_72),
% 4.92/1.03    inference(forward_demodulation,[],[f6813,f1090])).
% 4.92/1.03  fof(f6813,plain,(
% 4.92/1.03    k3_xboole_0(k4_xboole_0(k1_xboole_0,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | ~spl5_72),
% 4.92/1.03    inference(superposition,[],[f169,f4032])).
% 4.92/1.03  fof(f4032,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0)) | ~spl5_72),
% 4.92/1.03    inference(avatar_component_clause,[],[f4030])).
% 4.92/1.03  fof(f169,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 4.92/1.03    inference(superposition,[],[f70,f67])).
% 4.92/1.03  fof(f6525,plain,(
% 4.92/1.03    spl5_72 | ~spl5_60),
% 4.92/1.03    inference(avatar_split_clause,[],[f6524,f3325,f4030])).
% 4.92/1.03  fof(f3325,plain,(
% 4.92/1.03    spl5_60 <=> k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 4.92/1.03  fof(f6524,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0)) | ~spl5_60),
% 4.92/1.03    inference(forward_demodulation,[],[f6513,f470])).
% 4.92/1.03  fof(f6513,plain,(
% 4.92/1.03    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k1_xboole_0)) | ~spl5_60),
% 4.92/1.03    inference(superposition,[],[f175,f3327])).
% 4.92/1.03  fof(f3327,plain,(
% 4.92/1.03    k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | ~spl5_60),
% 4.92/1.03    inference(avatar_component_clause,[],[f3325])).
% 4.92/1.03  fof(f175,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 4.92/1.03    inference(forward_demodulation,[],[f163,f67])).
% 4.92/1.03  fof(f163,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 4.92/1.03    inference(superposition,[],[f67,f69])).
% 4.92/1.03  fof(f6512,plain,(
% 4.92/1.03    spl5_60),
% 4.92/1.03    inference(avatar_contradiction_clause,[],[f6511])).
% 4.92/1.03  fof(f6511,plain,(
% 4.92/1.03    $false | spl5_60),
% 4.92/1.03    inference(subsumption_resolution,[],[f6509,f78])).
% 4.92/1.03  fof(f6509,plain,(
% 4.92/1.03    ~r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | spl5_60),
% 4.92/1.03    inference(trivial_inequality_removal,[],[f6508])).
% 4.92/1.03  fof(f6508,plain,(
% 4.92/1.03    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | spl5_60),
% 4.92/1.03    inference(superposition,[],[f3326,f79])).
% 4.92/1.03  fof(f3326,plain,(
% 4.92/1.03    k1_xboole_0 != k2_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | spl5_60),
% 4.92/1.03    inference(avatar_component_clause,[],[f3325])).
% 4.92/1.03  fof(f6391,plain,(
% 4.92/1.03    spl5_19 | ~spl5_26),
% 4.92/1.03    inference(avatar_split_clause,[],[f5898,f1503,f1462])).
% 4.92/1.03  fof(f1462,plain,(
% 4.92/1.03    spl5_19 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 4.92/1.03  fof(f1503,plain,(
% 4.92/1.03    spl5_26 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 4.92/1.03  fof(f5898,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | ~spl5_26),
% 4.92/1.03    inference(forward_demodulation,[],[f5872,f470])).
% 4.92/1.03  fof(f5872,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))) | ~spl5_26),
% 4.92/1.03    inference(superposition,[],[f68,f1505])).
% 4.92/1.03  fof(f1505,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) | ~spl5_26),
% 4.92/1.03    inference(avatar_component_clause,[],[f1503])).
% 4.92/1.03  fof(f5369,plain,(
% 4.92/1.03    spl5_19 | ~spl5_1 | ~spl5_15 | ~spl5_61),
% 4.92/1.03    inference(avatar_split_clause,[],[f5368,f3331,f1388,f86,f1462])).
% 4.92/1.03  fof(f5368,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | (~spl5_1 | ~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f5367,f1090])).
% 4.92/1.03  fof(f5367,plain,(
% 4.92/1.03    k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | (~spl5_1 | ~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f5337,f4471])).
% 4.92/1.03  fof(f4471,plain,(
% 4.92/1.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f3619,f3787])).
% 4.92/1.03  fof(f3787,plain,(
% 4.92/1.03    ( ! [X13] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X13,sK2))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f3767,f470])).
% 4.92/1.03  fof(f3767,plain,(
% 4.92/1.03    ( ! [X13] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X13,sK2))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(superposition,[],[f70,f3703])).
% 4.92/1.03  fof(f3703,plain,(
% 4.92/1.03    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(backward_demodulation,[],[f3304,f3440])).
% 4.92/1.03  fof(f3440,plain,(
% 4.92/1.03    ( ! [X6] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f3439,f470])).
% 4.92/1.03  fof(f3439,plain,(
% 4.92/1.03    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f3438,f612])).
% 4.92/1.03  fof(f3438,plain,(
% 4.92/1.03    ( ! [X6] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k1_xboole_0))) ) | (~spl5_15 | ~spl5_61)),
% 4.92/1.03    inference(forward_demodulation,[],[f3397,f1390])).
% 4.92/1.03  fof(f3397,plain,(
% 4.92/1.03    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X6,k4_xboole_0(k1_xboole_0,sK2))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0)) ) | ~spl5_61),
% 4.92/1.03    inference(superposition,[],[f236,f3333])).
% 4.92/1.03  fof(f3304,plain,(
% 4.92/1.03    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ) | ~spl5_15),
% 4.92/1.03    inference(superposition,[],[f66,f1390])).
% 4.92/1.03  fof(f3619,plain,(
% 4.92/1.03    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))) ) | ~spl5_15),
% 4.92/1.03    inference(forward_demodulation,[],[f3618,f1090])).
% 4.92/1.03  fof(f3618,plain,(
% 4.92/1.03    ( ! [X0] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2))) ) | ~spl5_15),
% 4.92/1.03    inference(forward_demodulation,[],[f3588,f70])).
% 4.92/1.03  fof(f3588,plain,(
% 4.92/1.03    ( ! [X0] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2)))) ) | ~spl5_15),
% 4.92/1.03    inference(superposition,[],[f164,f3304])).
% 4.92/1.03  fof(f5337,plain,(
% 4.92/1.03    k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k1_xboole_0,sK2)) | ~spl5_1),
% 4.92/1.03    inference(superposition,[],[f2921,f1090])).
% 4.92/1.03  fof(f4758,plain,(
% 4.92/1.03    spl5_26 | ~spl5_12),
% 4.92/1.03    inference(avatar_split_clause,[],[f4722,f1358,f1503])).
% 4.92/1.03  fof(f1358,plain,(
% 4.92/1.03    spl5_12 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 4.92/1.03  fof(f4722,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) | ~spl5_12),
% 4.92/1.03    inference(superposition,[],[f131,f1360])).
% 4.92/1.03  fof(f1360,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_12),
% 4.92/1.03    inference(avatar_component_clause,[],[f1358])).
% 4.92/1.03  fof(f131,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.92/1.03    inference(forward_demodulation,[],[f126,f70])).
% 4.92/1.03  fof(f126,plain,(
% 4.92/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.92/1.03    inference(superposition,[],[f70,f69])).
% 4.92/1.03  fof(f4641,plain,(
% 4.92/1.03    spl5_1 | ~spl5_30 | ~spl5_80),
% 4.92/1.03    inference(avatar_split_clause,[],[f4640,f4161,f1545,f86])).
% 4.92/1.03  fof(f1545,plain,(
% 4.92/1.03    spl5_30 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0))),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 4.92/1.03  fof(f4640,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | (~spl5_30 | ~spl5_80)),
% 4.92/1.03    inference(forward_demodulation,[],[f1547,f4163])).
% 4.92/1.03  fof(f4163,plain,(
% 4.92/1.03    sK2 = k2_xboole_0(sK2,k1_xboole_0) | ~spl5_80),
% 4.92/1.03    inference(avatar_component_clause,[],[f4161])).
% 4.92/1.03  fof(f1547,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0)) | ~spl5_30),
% 4.92/1.03    inference(avatar_component_clause,[],[f1545])).
% 4.92/1.03  fof(f3673,plain,(
% 4.92/1.03    spl5_57 | ~spl5_61 | ~spl5_62),
% 4.92/1.03    inference(avatar_split_clause,[],[f3672,f3336,f3331,f3221])).
% 4.92/1.03  fof(f3672,plain,(
% 4.92/1.03    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl5_61 | ~spl5_62)),
% 4.92/1.03    inference(forward_demodulation,[],[f3338,f3333])).
% 4.92/1.03  fof(f3338,plain,(
% 4.92/1.03    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) | ~spl5_62),
% 4.92/1.03    inference(avatar_component_clause,[],[f3336])).
% 4.92/1.03  fof(f2906,plain,(
% 4.92/1.03    ~spl5_3 | ~spl5_48),
% 4.92/1.03    inference(avatar_contradiction_clause,[],[f2905])).
% 4.92/1.03  fof(f2905,plain,(
% 4.92/1.03    $false | (~spl5_3 | ~spl5_48)),
% 4.92/1.03    inference(subsumption_resolution,[],[f2896,f71])).
% 4.92/1.03  fof(f2896,plain,(
% 4.92/1.03    ~r1_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) | (~spl5_3 | ~spl5_48)),
% 4.92/1.03    inference(resolution,[],[f2643,f1392])).
% 4.92/1.03  fof(f1392,plain,(
% 4.92/1.03    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r1_xboole_0(X0,sK2)) ) | ~spl5_3),
% 4.92/1.03    inference(resolution,[],[f95,f63])).
% 4.92/1.03  fof(f63,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 4.92/1.03    inference(cnf_transformation,[],[f44])).
% 4.92/1.03  fof(f44,plain,(
% 4.92/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.92/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f43])).
% 4.92/1.03  fof(f43,plain,(
% 4.92/1.03    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 4.92/1.03    introduced(choice_axiom,[])).
% 4.92/1.03  fof(f27,plain,(
% 4.92/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.92/1.03    inference(ennf_transformation,[],[f24])).
% 4.92/1.03  fof(f24,plain,(
% 4.92/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.92/1.03    inference(rectify,[],[f3])).
% 4.92/1.03  fof(f3,axiom,(
% 4.92/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.92/1.03  fof(f95,plain,(
% 4.92/1.03    r2_hidden(sK1,sK2) | ~spl5_3),
% 4.92/1.03    inference(avatar_component_clause,[],[f94])).
% 4.92/1.03  fof(f2643,plain,(
% 4.92/1.03    r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl5_48),
% 4.92/1.03    inference(avatar_component_clause,[],[f2641])).
% 4.92/1.03  fof(f2641,plain,(
% 4.92/1.03    spl5_48 <=> r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 4.92/1.03  fof(f2890,plain,(
% 4.92/1.03    ~spl5_2 | ~spl5_37),
% 4.92/1.03    inference(avatar_contradiction_clause,[],[f2889])).
% 4.92/1.03  fof(f2889,plain,(
% 4.92/1.03    $false | (~spl5_2 | ~spl5_37)),
% 4.92/1.03    inference(subsumption_resolution,[],[f2882,f71])).
% 4.92/1.03  fof(f2882,plain,(
% 4.92/1.03    ~r1_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) | (~spl5_2 | ~spl5_37)),
% 4.92/1.03    inference(resolution,[],[f2139,f1526])).
% 4.92/1.03  fof(f1526,plain,(
% 4.92/1.03    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_xboole_0(X0,sK2)) ) | ~spl5_2),
% 4.92/1.03    inference(resolution,[],[f91,f63])).
% 4.92/1.03  fof(f91,plain,(
% 4.92/1.03    r2_hidden(sK0,sK2) | ~spl5_2),
% 4.92/1.03    inference(avatar_component_clause,[],[f90])).
% 4.92/1.03  fof(f2139,plain,(
% 4.92/1.03    r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl5_37),
% 4.92/1.03    inference(avatar_component_clause,[],[f2138])).
% 4.92/1.03  fof(f2138,plain,(
% 4.92/1.03    spl5_37 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 4.92/1.03  fof(f2680,plain,(
% 4.92/1.03    spl5_37 | spl5_48 | ~spl5_19 | spl5_11),
% 4.92/1.03    inference(avatar_split_clause,[],[f2588,f1352,f1462,f2641,f2138])).
% 4.92/1.03  fof(f1352,plain,(
% 4.92/1.03    spl5_11 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),sK2),k1_xboole_0)),
% 4.92/1.03    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 4.92/1.03  fof(f2588,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) != k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl5_11),
% 4.92/1.03    inference(superposition,[],[f1353,f261])).
% 4.92/1.03  fof(f261,plain,(
% 4.92/1.03    ( ! [X6,X8,X7] : (k2_tarski(X6,X7) = k3_xboole_0(k2_tarski(X6,X7),X8) | r2_hidden(X7,k4_xboole_0(k2_tarski(X6,X7),X8)) | r2_hidden(X6,k4_xboole_0(k2_tarski(X6,X7),X8))) )),
% 4.92/1.03    inference(superposition,[],[f58,f70])).
% 4.92/1.03  fof(f58,plain,(
% 4.92/1.03    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 4.92/1.03    inference(cnf_transformation,[],[f41])).
% 4.92/1.03  fof(f1353,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) != k2_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),sK2),k1_xboole_0) | spl5_11),
% 4.92/1.03    inference(avatar_component_clause,[],[f1352])).
% 4.92/1.03  fof(f2679,plain,(
% 4.92/1.03    spl5_37 | spl5_48 | spl5_12),
% 4.92/1.03    inference(avatar_split_clause,[],[f2632,f1358,f2641,f2138])).
% 4.92/1.03  fof(f2632,plain,(
% 4.92/1.03    r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl5_12),
% 4.92/1.03    inference(trivial_inequality_removal,[],[f2589])).
% 4.92/1.03  fof(f2589,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl5_12),
% 4.92/1.03    inference(superposition,[],[f1359,f261])).
% 4.92/1.03  fof(f1359,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),sK2) | spl5_12),
% 4.92/1.03    inference(avatar_component_clause,[],[f1358])).
% 4.92/1.03  fof(f1548,plain,(
% 4.92/1.03    spl5_30 | ~spl5_11),
% 4.92/1.03    inference(avatar_split_clause,[],[f1543,f1352,f1545])).
% 4.92/1.03  fof(f1543,plain,(
% 4.92/1.03    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0)) | ~spl5_11),
% 4.92/1.03    inference(forward_demodulation,[],[f1532,f470])).
% 4.92/1.03  fof(f1532,plain,(
% 4.92/1.03    k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k4_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k1_xboole_0)) | ~spl5_11),
% 4.92/1.03    inference(superposition,[],[f175,f1354])).
% 4.92/1.03  fof(f1354,plain,(
% 4.92/1.03    k2_tarski(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),sK2),k1_xboole_0) | ~spl5_11),
% 4.92/1.03    inference(avatar_component_clause,[],[f1352])).
% 4.92/1.03  fof(f99,plain,(
% 4.92/1.03    spl5_1 | spl5_2),
% 4.92/1.03    inference(avatar_split_clause,[],[f47,f90,f86])).
% 4.92/1.03  fof(f47,plain,(
% 4.92/1.03    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.92/1.03    inference(cnf_transformation,[],[f35])).
% 4.92/1.03  fof(f35,plain,(
% 4.92/1.03    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 4.92/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).
% 4.92/1.03  fof(f34,plain,(
% 4.92/1.03    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 4.92/1.03    introduced(choice_axiom,[])).
% 4.92/1.03  fof(f33,plain,(
% 4.92/1.03    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.92/1.03    inference(flattening,[],[f32])).
% 4.92/1.03  fof(f32,plain,(
% 4.92/1.03    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.92/1.03    inference(nnf_transformation,[],[f26])).
% 4.92/1.03  fof(f26,plain,(
% 4.92/1.03    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.92/1.03    inference(ennf_transformation,[],[f23])).
% 4.92/1.03  fof(f23,negated_conjecture,(
% 4.92/1.03    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.92/1.03    inference(negated_conjecture,[],[f22])).
% 4.92/1.03  fof(f22,conjecture,(
% 4.92/1.03    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 4.92/1.03  fof(f98,plain,(
% 4.92/1.03    spl5_1 | spl5_3),
% 4.92/1.03    inference(avatar_split_clause,[],[f48,f94,f86])).
% 4.92/1.03  fof(f48,plain,(
% 4.92/1.03    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.92/1.03    inference(cnf_transformation,[],[f35])).
% 4.92/1.03  fof(f97,plain,(
% 4.92/1.03    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 4.92/1.03    inference(avatar_split_clause,[],[f49,f94,f90,f86])).
% 4.92/1.03  fof(f49,plain,(
% 4.92/1.03    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.92/1.03    inference(cnf_transformation,[],[f35])).
% 4.92/1.03  % SZS output end Proof for theBenchmark
% 4.92/1.03  % (31909)------------------------------
% 4.92/1.03  % (31909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.92/1.03  % (31909)Termination reason: Refutation
% 4.92/1.03  
% 4.92/1.03  % (31909)Memory used [KB]: 11641
% 4.92/1.03  % (31909)Time elapsed: 0.622 s
% 4.92/1.03  % (31909)------------------------------
% 4.92/1.03  % (31909)------------------------------
% 4.92/1.04  % (31887)Success in time 0.675 s
%------------------------------------------------------------------------------
