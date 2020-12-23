%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:12 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 144 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 373 expanded)
%              Number of equality atoms :   57 ( 127 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f205,f215,f522,f554,f568,f627,f681,f725,f728])).

fof(f728,plain,
    ( spl9_2
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | spl9_2
    | ~ spl9_16 ),
    inference(resolution,[],[f689,f117])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f689,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl9_2
    | ~ spl9_16 ),
    inference(backward_demodulation,[],[f203,f682])).

fof(f682,plain,
    ( sK2 = sK3
    | ~ spl9_16 ),
    inference(resolution,[],[f626,f121])).

fof(f121,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

% (10838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f626,plain,
    ( r2_hidden(sK3,k1_tarski(sK2))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl9_16
  <=> r2_hidden(sK3,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f203,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl9_2
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f725,plain,
    ( spl9_1
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | spl9_1
    | ~ spl9_16 ),
    inference(resolution,[],[f688,f117])).

fof(f688,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl9_1
    | ~ spl9_16 ),
    inference(backward_demodulation,[],[f199,f682])).

fof(f199,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl9_1
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f681,plain,(
    spl9_15 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | spl9_15 ),
    inference(resolution,[],[f622,f127])).

fof(f127,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f70,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f622,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k2_xboole_0(sK4,k1_tarski(sK2)))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f620])).

fof(f620,plain,
    ( spl9_15
  <=> r1_tarski(k1_tarski(sK2),k2_xboole_0(sK4,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f627,plain,
    ( ~ spl9_15
    | spl9_16
    | spl9_5 ),
    inference(avatar_split_clause,[],[f600,f547,f624,f620])).

fof(f547,plain,
    ( spl9_5
  <=> r1_tarski(k1_tarski(sK2),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f600,plain,
    ( r2_hidden(sK3,k1_tarski(sK2))
    | ~ r1_tarski(k1_tarski(sK2),k2_xboole_0(sK4,k1_tarski(sK2)))
    | spl9_5 ),
    inference(resolution,[],[f95,f549])).

fof(f549,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f547])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_zfmisc_1)).

fof(f568,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | spl9_6 ),
    inference(resolution,[],[f559,f70])).

fof(f559,plain,
    ( ~ r1_tarski(sK4,k2_xboole_0(sK4,k1_tarski(sK2)))
    | spl9_6 ),
    inference(resolution,[],[f553,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

% (10863)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f553,plain,
    ( ~ r1_tarski(k4_xboole_0(sK4,k1_tarski(sK3)),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl9_6
  <=> r1_tarski(k4_xboole_0(sK4,k1_tarski(sK3)),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f554,plain,
    ( ~ spl9_5
    | ~ spl9_6
    | spl9_4 ),
    inference(avatar_split_clause,[],[f535,f211,f551,f547])).

fof(f211,plain,
    ( spl9_4
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f535,plain,
    ( ~ r1_tarski(k4_xboole_0(sK4,k1_tarski(sK3)),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))
    | ~ r1_tarski(k1_tarski(sK2),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))
    | spl9_4 ),
    inference(resolution,[],[f97,f213])).

fof(f213,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f211])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

% (10844)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f522,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | spl9_3 ),
    inference(resolution,[],[f397,f427])).

fof(f427,plain,
    ( ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))
    | spl9_3 ),
    inference(forward_demodulation,[],[f426,f393])).

fof(f393,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f90,f72])).

fof(f90,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f426,plain,
    ( ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),sK4)))
    | spl9_3 ),
    inference(forward_demodulation,[],[f425,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f425,plain,
    ( ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k4_xboole_0(sK4,k1_tarski(sK3)))))
    | spl9_3 ),
    inference(forward_demodulation,[],[f424,f72])).

fof(f424,plain,
    ( ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3))))
    | spl9_3 ),
    inference(backward_demodulation,[],[f328,f393])).

fof(f328,plain,
    ( ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3)))))
    | spl9_3 ),
    inference(resolution,[],[f96,f209])).

fof(f209,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl9_3
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f397,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f70,f90])).

fof(f215,plain,
    ( ~ spl9_4
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f185,f207,f211])).

fof(f185,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) ),
    inference(extensionality_resolution,[],[f79,f125])).

fof(f125,plain,(
    k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))) ),
    inference(backward_demodulation,[],[f69,f72])).

fof(f69,plain,(
    k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK2))
    & sK2 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK2))
      & sK2 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f205,plain,
    ( ~ spl9_2
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f183,f197,f201])).

fof(f183,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK3,sK2) ),
    inference(extensionality_resolution,[],[f79,f68])).

fof(f68,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (10846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.51  % (10854)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.20/0.51  % (10862)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.20/0.52  % (10834)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.52  % (10854)Refutation not found, incomplete strategy% (10854)------------------------------
% 1.20/0.52  % (10854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (10839)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % (10854)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (10854)Memory used [KB]: 10746
% 1.20/0.52  % (10854)Time elapsed: 0.108 s
% 1.20/0.52  % (10854)------------------------------
% 1.20/0.52  % (10854)------------------------------
% 1.20/0.52  % (10835)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (10835)Refutation not found, incomplete strategy% (10835)------------------------------
% 1.20/0.52  % (10835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (10835)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (10835)Memory used [KB]: 10746
% 1.20/0.52  % (10835)Time elapsed: 0.115 s
% 1.20/0.52  % (10835)------------------------------
% 1.20/0.52  % (10835)------------------------------
% 1.20/0.53  % (10849)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.53  % (10846)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % (10847)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f729,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(avatar_sat_refutation,[],[f205,f215,f522,f554,f568,f627,f681,f725,f728])).
% 1.20/0.53  fof(f728,plain,(
% 1.20/0.53    spl9_2 | ~spl9_16),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f727])).
% 1.20/0.53  fof(f727,plain,(
% 1.20/0.53    $false | (spl9_2 | ~spl9_16)),
% 1.20/0.53    inference(resolution,[],[f689,f117])).
% 1.20/0.53  fof(f117,plain,(
% 1.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.20/0.53    inference(equality_resolution,[],[f78])).
% 1.20/0.53  fof(f78,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.20/0.53    inference(cnf_transformation,[],[f46])).
% 1.20/0.53  fof(f46,plain,(
% 1.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.53    inference(flattening,[],[f45])).
% 1.20/0.53  fof(f45,plain,(
% 1.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.53    inference(nnf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.20/0.53  fof(f689,plain,(
% 1.20/0.53    ~r1_tarski(sK2,sK2) | (spl9_2 | ~spl9_16)),
% 1.20/0.53    inference(backward_demodulation,[],[f203,f682])).
% 1.20/0.53  fof(f682,plain,(
% 1.20/0.53    sK2 = sK3 | ~spl9_16),
% 1.20/0.53    inference(resolution,[],[f626,f121])).
% 1.20/0.53  fof(f121,plain,(
% 1.20/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.20/0.53    inference(equality_resolution,[],[f80])).
% 1.20/0.53  fof(f80,plain,(
% 1.20/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.20/0.53    inference(cnf_transformation,[],[f50])).
% 1.20/0.53  fof(f50,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 1.20/0.53  % (10838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.20/0.53    inference(rectify,[],[f47])).
% 1.20/0.53  fof(f47,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.20/0.53    inference(nnf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,axiom,(
% 1.20/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.20/0.53  fof(f626,plain,(
% 1.20/0.53    r2_hidden(sK3,k1_tarski(sK2)) | ~spl9_16),
% 1.20/0.53    inference(avatar_component_clause,[],[f624])).
% 1.20/0.53  fof(f624,plain,(
% 1.20/0.53    spl9_16 <=> r2_hidden(sK3,k1_tarski(sK2))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.20/0.53  fof(f203,plain,(
% 1.20/0.53    ~r1_tarski(sK3,sK2) | spl9_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f201])).
% 1.20/0.53  fof(f201,plain,(
% 1.20/0.53    spl9_2 <=> r1_tarski(sK3,sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.20/0.53  fof(f725,plain,(
% 1.20/0.53    spl9_1 | ~spl9_16),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f724])).
% 1.20/0.53  fof(f724,plain,(
% 1.20/0.53    $false | (spl9_1 | ~spl9_16)),
% 1.20/0.53    inference(resolution,[],[f688,f117])).
% 1.20/0.53  fof(f688,plain,(
% 1.20/0.53    ~r1_tarski(sK2,sK2) | (spl9_1 | ~spl9_16)),
% 1.20/0.53    inference(backward_demodulation,[],[f199,f682])).
% 1.20/0.53  fof(f199,plain,(
% 1.20/0.53    ~r1_tarski(sK2,sK3) | spl9_1),
% 1.20/0.53    inference(avatar_component_clause,[],[f197])).
% 1.20/0.53  fof(f197,plain,(
% 1.20/0.53    spl9_1 <=> r1_tarski(sK2,sK3)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.20/0.53  fof(f681,plain,(
% 1.20/0.53    spl9_15),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f678])).
% 1.20/0.53  fof(f678,plain,(
% 1.20/0.53    $false | spl9_15),
% 1.20/0.53    inference(resolution,[],[f622,f127])).
% 1.20/0.53  fof(f127,plain,(
% 1.20/0.53    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 1.20/0.53    inference(superposition,[],[f70,f72])).
% 1.20/0.53  fof(f72,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.20/0.53  fof(f70,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f14])).
% 1.20/0.53  fof(f14,axiom,(
% 1.20/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.20/0.53  fof(f622,plain,(
% 1.20/0.53    ~r1_tarski(k1_tarski(sK2),k2_xboole_0(sK4,k1_tarski(sK2))) | spl9_15),
% 1.20/0.53    inference(avatar_component_clause,[],[f620])).
% 1.20/0.53  fof(f620,plain,(
% 1.20/0.53    spl9_15 <=> r1_tarski(k1_tarski(sK2),k2_xboole_0(sK4,k1_tarski(sK2)))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.20/0.53  fof(f627,plain,(
% 1.20/0.53    ~spl9_15 | spl9_16 | spl9_5),
% 1.20/0.53    inference(avatar_split_clause,[],[f600,f547,f624,f620])).
% 1.20/0.53  fof(f547,plain,(
% 1.20/0.53    spl9_5 <=> r1_tarski(k1_tarski(sK2),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.20/0.53  fof(f600,plain,(
% 1.20/0.53    r2_hidden(sK3,k1_tarski(sK2)) | ~r1_tarski(k1_tarski(sK2),k2_xboole_0(sK4,k1_tarski(sK2))) | spl9_5),
% 1.20/0.53    inference(resolution,[],[f95,f549])).
% 1.20/0.53  fof(f549,plain,(
% 1.20/0.53    ~r1_tarski(k1_tarski(sK2),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) | spl9_5),
% 1.20/0.53    inference(avatar_component_clause,[],[f547])).
% 1.20/0.53  fof(f95,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f32])).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1))),
% 1.20/0.53    inference(flattening,[],[f31])).
% 1.20/0.53  fof(f31,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f19])).
% 1.20/0.53  fof(f19,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_zfmisc_1)).
% 1.20/0.53  fof(f568,plain,(
% 1.20/0.53    spl9_6),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f565])).
% 1.20/0.53  fof(f565,plain,(
% 1.20/0.53    $false | spl9_6),
% 1.20/0.53    inference(resolution,[],[f559,f70])).
% 1.20/0.53  fof(f559,plain,(
% 1.20/0.53    ~r1_tarski(sK4,k2_xboole_0(sK4,k1_tarski(sK2))) | spl9_6),
% 1.20/0.53    inference(resolution,[],[f553,f94])).
% 1.20/0.53  fof(f94,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f30])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f8])).
% 1.20/0.53  fof(f8,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).
% 1.30/0.53  % (10863)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.53  fof(f553,plain,(
% 1.30/0.53    ~r1_tarski(k4_xboole_0(sK4,k1_tarski(sK3)),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) | spl9_6),
% 1.30/0.53    inference(avatar_component_clause,[],[f551])).
% 1.30/0.53  fof(f551,plain,(
% 1.30/0.53    spl9_6 <=> r1_tarski(k4_xboole_0(sK4,k1_tarski(sK3)),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.30/0.53  fof(f554,plain,(
% 1.30/0.53    ~spl9_5 | ~spl9_6 | spl9_4),
% 1.30/0.53    inference(avatar_split_clause,[],[f535,f211,f551,f547])).
% 1.30/0.53  fof(f211,plain,(
% 1.30/0.53    spl9_4 <=> r1_tarski(k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.30/0.53  fof(f535,plain,(
% 1.30/0.53    ~r1_tarski(k4_xboole_0(sK4,k1_tarski(sK3)),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) | ~r1_tarski(k1_tarski(sK2),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) | spl9_4),
% 1.30/0.53    inference(resolution,[],[f97,f213])).
% 1.30/0.53  fof(f213,plain,(
% 1.30/0.53    ~r1_tarski(k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3))) | spl9_4),
% 1.30/0.53    inference(avatar_component_clause,[],[f211])).
% 1.30/0.53  fof(f97,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.30/0.53    inference(flattening,[],[f34])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.30/0.53  % (10844)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  fof(f522,plain,(
% 1.30/0.53    spl9_3),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f499])).
% 1.30/0.53  fof(f499,plain,(
% 1.30/0.53    $false | spl9_3),
% 1.30/0.53    inference(resolution,[],[f397,f427])).
% 1.30/0.53  fof(f427,plain,(
% 1.30/0.53    ~r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) | spl9_3),
% 1.30/0.53    inference(forward_demodulation,[],[f426,f393])).
% 1.30/0.53  fof(f393,plain,(
% 1.30/0.53    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 1.30/0.53    inference(superposition,[],[f90,f72])).
% 1.30/0.53  fof(f90,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.30/0.53  fof(f426,plain,(
% 1.30/0.53    ~r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),sK4))) | spl9_3),
% 1.30/0.53    inference(forward_demodulation,[],[f425,f73])).
% 1.30/0.53  fof(f73,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f10])).
% 1.30/0.53  fof(f10,axiom,(
% 1.30/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.30/0.53  fof(f425,plain,(
% 1.30/0.53    ~r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k4_xboole_0(sK4,k1_tarski(sK3))))) | spl9_3),
% 1.30/0.53    inference(forward_demodulation,[],[f424,f72])).
% 1.30/0.53  fof(f424,plain,(
% 1.30/0.53    ~r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)))) | spl9_3),
% 1.30/0.53    inference(backward_demodulation,[],[f328,f393])).
% 1.30/0.53  fof(f328,plain,(
% 1.30/0.53    ~r1_tarski(k2_xboole_0(sK4,k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))))) | spl9_3),
% 1.30/0.53    inference(resolution,[],[f96,f209])).
% 1.30/0.53  fof(f209,plain,(
% 1.30/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3)))) | spl9_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f207])).
% 1.30/0.53  fof(f207,plain,(
% 1.30/0.53    spl9_3 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.30/0.53  fof(f96,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f12])).
% 1.30/0.53  fof(f12,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.30/0.53  fof(f397,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 1.30/0.53    inference(superposition,[],[f70,f90])).
% 1.30/0.53  fof(f215,plain,(
% 1.30/0.53    ~spl9_4 | ~spl9_3),
% 1.30/0.53    inference(avatar_split_clause,[],[f185,f207,f211])).
% 1.30/0.53  fof(f185,plain,(
% 1.30/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3)))) | ~r1_tarski(k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3))),k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)))),
% 1.30/0.53    inference(extensionality_resolution,[],[f79,f125])).
% 1.30/0.53  fof(f125,plain,(
% 1.30/0.53    k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK4,k1_tarski(sK3)))),
% 1.30/0.53    inference(backward_demodulation,[],[f69,f72])).
% 1.30/0.53  fof(f69,plain,(
% 1.30/0.53    k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK2))),
% 1.30/0.53    inference(cnf_transformation,[],[f41])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK2)) & sK2 != sK3),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1) => (k4_xboole_0(k2_xboole_0(sK4,k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK2)) & sK2 != sK3)),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 1.30/0.53    inference(ennf_transformation,[],[f24])).
% 1.30/0.53  fof(f24,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 1.30/0.53    inference(negated_conjecture,[],[f23])).
% 1.30/0.53  fof(f23,conjecture,(
% 1.30/0.53    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 1.30/0.53  fof(f79,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f46])).
% 1.30/0.53  fof(f205,plain,(
% 1.30/0.53    ~spl9_2 | ~spl9_1),
% 1.30/0.53    inference(avatar_split_clause,[],[f183,f197,f201])).
% 1.30/0.53  fof(f183,plain,(
% 1.30/0.53    ~r1_tarski(sK2,sK3) | ~r1_tarski(sK3,sK2)),
% 1.30/0.53    inference(extensionality_resolution,[],[f79,f68])).
% 1.30/0.53  fof(f68,plain,(
% 1.30/0.53    sK2 != sK3),
% 1.30/0.53    inference(cnf_transformation,[],[f41])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (10846)------------------------------
% 1.30/0.53  % (10846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (10846)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (10846)Memory used [KB]: 6652
% 1.30/0.53  % (10846)Time elapsed: 0.108 s
% 1.30/0.53  % (10846)------------------------------
% 1.30/0.53  % (10846)------------------------------
% 1.30/0.54  % (10837)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (10831)Success in time 0.173 s
%------------------------------------------------------------------------------
