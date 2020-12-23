%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t72_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 222 expanded)
%              Number of leaves         :   24 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  232 ( 553 expanded)
%              Number of equality atoms :   51 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f63,f82,f89,f102,f138,f147,f157,f164,f185,f195,f219,f231,f251,f253])).

fof(f253,plain,
    ( ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f146,f238])).

fof(f238,plain,
    ( ! [X1] : k4_xboole_0(sK2,k2_tarski(sK0,X1)) != sK2
    | ~ spl3_6 ),
    inference(resolution,[],[f232,f67])).

fof(f67,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) != X2 ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',t83_xboole_1)).

fof(f232,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',t55_zfmisc_1)).

fof(f78,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f146,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_12
  <=> k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f251,plain,
    ( spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f217,f74,f145])).

fof(f74,plain,
    ( spl3_4
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f217,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f216])).

fof(f216,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2
    | ~ spl3_4 ),
    inference(superposition,[],[f68,f75])).

fof(f75,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | k4_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f231,plain,
    ( spl3_5
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f229,f72])).

fof(f72,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_5
  <=> k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f229,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_12 ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,
    ( sK2 != sK2
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f68,f146])).

fof(f219,plain,
    ( ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f217,f207])).

fof(f207,plain,
    ( ! [X1] : k4_xboole_0(sK2,k2_tarski(X1,sK1)) != sK2
    | ~ spl3_8 ),
    inference(resolution,[],[f203,f67])).

fof(f203,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(X0,sK1),sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f186,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',commutativity_k2_tarski)).

fof(f186,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,X0),sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f85,f48])).

fof(f85,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f195,plain,
    ( ~ spl3_19
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f187,f84,f193])).

fof(f193,plain,
    ( spl3_19
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f187,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f185,plain,
    ( ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f183])).

fof(f183,plain,
    ( sK2 != sK2
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f170,f137])).

fof(f137,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK0)) = sK2
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_10
  <=> k4_xboole_0(sK2,k2_tarski(sK0,sK0)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f170,plain,
    ( ! [X1] : k4_xboole_0(sK2,k2_tarski(sK0,X1)) != sK2
    | ~ spl3_6 ),
    inference(resolution,[],[f148,f67])).

fof(f148,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f48])).

fof(f164,plain,
    ( ~ spl3_17
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f149,f77,f162])).

fof(f162,plain,
    ( spl3_17
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f149,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f42])).

fof(f157,plain,
    ( ~ spl3_15
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f150,f77,f155])).

fof(f155,plain,
    ( spl3_15
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',t7_boole)).

fof(f147,plain,
    ( spl3_12
    | spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f131,f87,f80,f145])).

fof(f80,plain,
    ( spl3_7
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f87,plain,
    ( spl3_9
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f131,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f106,f88])).

fof(f88,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f106,plain,
    ( ! [X10] :
        ( r2_hidden(X10,sK2)
        | k4_xboole_0(sK2,k2_tarski(sK0,X10)) = sK2 )
    | ~ spl3_7 ),
    inference(resolution,[],[f98,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k4_xboole_0(X1,k2_tarski(X0,X2)) = X1 ) ),
    inference(resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X4,k2_tarski(X5,X3))
      | r2_hidden(X5,X4)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',t57_zfmisc_1)).

fof(f138,plain,
    ( spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f130,f80,f136])).

fof(f130,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK0)) = sK2
    | ~ spl3_7 ),
    inference(resolution,[],[f106,f81])).

fof(f102,plain,
    ( ~ spl3_5
    | spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f34,f84,f77,f71])).

fof(f34,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',t72_zfmisc_1)).

fof(f89,plain,
    ( spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f33,f87,f74])).

fof(f33,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,
    ( spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f32,f80,f74])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f61,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',d2_xboole_0)).

fof(f56,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f49,f54])).

fof(f54,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f35,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t72_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
