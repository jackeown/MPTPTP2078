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
% DateTime   : Thu Dec  3 13:00:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 427 expanded)
%              Number of leaves         :   17 (  97 expanded)
%              Depth                    :   22
%              Number of atoms          :  446 (1431 expanded)
%              Number of equality atoms :   59 ( 272 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f286,f323,f339,f380])).

fof(f380,plain,
    ( ~ spl9_1
    | ~ spl9_13
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_13
    | spl9_15 ),
    inference(subsumption_resolution,[],[f378,f36])).

fof(f36,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f378,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl9_1
    | ~ spl9_13
    | spl9_15 ),
    inference(backward_demodulation,[],[f322,f376])).

fof(f376,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl9_1
    | ~ spl9_13 ),
    inference(resolution,[],[f375,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f375,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl9_1
    | ~ spl9_13 ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl9_1
    | ~ spl9_13 ),
    inference(resolution,[],[f367,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_wellord2(sK1),X0),X0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f103,f35])).

fof(f35,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f102,f89])).

fof(f89,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

% (20526)Refutation not found, incomplete strategy% (20526)------------------------------
% (20526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

% (20526)Termination reason: Refutation not found, incomplete strategy

% (20526)Memory used [KB]: 6140
% (20526)Time elapsed: 0.118 s
% (20526)------------------------------
% (20526)------------------------------
fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X1)
      | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f101,f39])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X1)
      | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(k3_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),X1)
          | ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & r1_tarski(k1_wellord1(X0,X2),X1)
              & r2_hidden(X2,k3_relat_1(X0)) ) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),X1)
          | ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & r1_tarski(k1_wellord1(X0,X2),X1)
              & r2_hidden(X2,k3_relat_1(X0)) ) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( ! [X2] :
                ( ( r1_tarski(k1_wellord1(X0,X2),X1)
                  & r2_hidden(X2,k3_relat_1(X0)) )
               => r2_hidden(X2,X1) )
           => r1_tarski(k3_relat_1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_wellord1)).

fof(f367,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k1_wellord2(sK1),X1),sK0)
        | r1_tarski(sK1,X1) )
    | ~ spl9_1
    | ~ spl9_13 ),
    inference(resolution,[],[f354,f191])).

fof(f191,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(sK1),X0),sK1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f190,f35])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | r2_hidden(sK2(k1_wellord2(X0),X1),X0) ) ),
    inference(resolution,[],[f189,f51])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(k1_wellord2(X0))
      | r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f188,f39])).

fof(f188,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f40,f89])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k3_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f354,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(X4,sK0) )
    | ~ spl9_1
    | ~ spl9_13 ),
    inference(forward_demodulation,[],[f350,f124])).

fof(f124,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl9_1
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f350,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k1_wellord1(k1_wellord2(sK0),sK1)) )
    | ~ spl9_13 ),
    inference(resolution,[],[f261,f312])).

fof(f312,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl9_13
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f261,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k1_wellord1(k1_wellord2(sK0),X3)) ) ),
    inference(resolution,[],[f258,f38])).

fof(f38,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f258,plain,(
    ! [X4,X5,X3] :
      ( ~ v3_ordinal1(X4)
      | r2_hidden(X5,X4)
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X5,k1_wellord1(k1_wellord2(X4),X3)) ) ),
    inference(resolution,[],[f256,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X2),X1)) ) ),
    inference(resolution,[],[f74,f39])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X2,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f255,f89])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0))
      | r2_hidden(X2,k3_relat_1(k1_wellord2(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f254,f89])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0))
      | r2_hidden(X2,k3_relat_1(k1_wellord2(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f253,f39])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0))
      | r2_hidden(X2,k3_relat_1(k1_wellord2(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X4,X3,X1] :
      ( ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,k3_relat_1(X1))
      | ~ r2_hidden(k4_tarski(X4,X3),X1)
      | r2_hidden(X4,k3_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f78,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X4,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(k3_relat_1(X1),k3_relat_1(X1))
      | ~ r2_hidden(X3,k3_relat_1(X1))
      | ~ r2_hidden(k4_tarski(X4,X3),X1)
      | r2_hidden(X4,k3_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X1)
      | r2_hidden(X4,X0)
      | k3_relat_1(X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

% (20532)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(f322,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl9_15
  <=> r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f339,plain,
    ( spl9_2
    | spl9_13 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl9_2
    | spl9_13 ),
    inference(subsumption_resolution,[],[f337,f35])).

fof(f337,plain,
    ( ~ v3_ordinal1(sK1)
    | spl9_2
    | spl9_13 ),
    inference(subsumption_resolution,[],[f336,f37])).

fof(f37,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f336,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | spl9_2
    | spl9_13 ),
    inference(subsumption_resolution,[],[f329,f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl9_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f329,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | spl9_13 ),
    inference(resolution,[],[f313,f109])).

fof(f109,plain,(
    ! [X1] :
      ( r2_hidden(sK0,X1)
      | r2_hidden(X1,sK0)
      | sK0 = X1
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f313,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f311])).

fof(f323,plain,
    ( ~ spl9_13
    | ~ spl9_15
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f318,f122,f320,f311])).

fof(f318,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f308,f38])).

fof(f308,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl9_1 ),
    inference(superposition,[],[f212,f124])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f211,f89])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f210,f39])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f43,f51])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f286,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f284,f98])).

fof(f98,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f97,f36])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f95,f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f284,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f219,f282])).

fof(f282,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl9_2 ),
    inference(resolution,[],[f281,f69])).

fof(f281,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f279,f192])).

fof(f192,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_wellord2(sK0),X1),sK0)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f190,f38])).

fof(f279,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK1),sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl9_2 ),
    inference(resolution,[],[f271,f105])).

fof(f105,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k1_wellord2(sK0),X1),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f103,f38])).

fof(f271,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f264,f148])).

fof(f148,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f147,f38])).

fof(f147,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl9_2 ),
    inference(resolution,[],[f128,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f128,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f264,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(X2,k1_wellord1(k1_wellord2(sK1),sK0)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f260,f128])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_wellord1(k1_wellord2(sK1),X1)) ) ),
    inference(resolution,[],[f258,f35])).

fof(f219,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f218,f35])).

fof(f218,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ v3_ordinal1(sK1)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f217,f128])).

fof(f217,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl9_2 ),
    inference(superposition,[],[f212,f148])).

fof(f129,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f119,f35])).

fof(f119,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f118,f38])).

fof(f118,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f112,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f108,f107])).

fof(f107,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(sK0),X1) = X1 ) ),
    inference(resolution,[],[f52,f38])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | r2_hidden(X0,sK1)
      | sK1 = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f53,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (20517)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (20522)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (20518)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (20524)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (20535)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (20515)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (20514)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (20520)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (20527)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (20520)Refutation not found, incomplete strategy% (20520)------------------------------
% 0.20/0.51  % (20520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20529)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (20520)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20520)Memory used [KB]: 1663
% 0.20/0.51  % (20520)Time elapsed: 0.094 s
% 0.20/0.51  % (20520)------------------------------
% 0.20/0.51  % (20520)------------------------------
% 0.20/0.51  % (20533)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (20519)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (20514)Refutation not found, incomplete strategy% (20514)------------------------------
% 0.20/0.51  % (20514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20514)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20514)Memory used [KB]: 10618
% 0.20/0.51  % (20514)Time elapsed: 0.104 s
% 0.20/0.51  % (20514)------------------------------
% 0.20/0.51  % (20514)------------------------------
% 0.20/0.52  % (20528)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (20534)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (20519)Refutation not found, incomplete strategy% (20519)------------------------------
% 0.20/0.52  % (20519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20519)Memory used [KB]: 10874
% 0.20/0.52  % (20519)Time elapsed: 0.069 s
% 0.20/0.52  % (20519)------------------------------
% 0.20/0.52  % (20519)------------------------------
% 0.20/0.52  % (20531)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (20537)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (20525)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (20516)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (20526)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (20535)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f382,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f129,f286,f323,f339,f380])).
% 0.20/0.52  fof(f380,plain,(
% 0.20/0.52    ~spl9_1 | ~spl9_13 | spl9_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f379])).
% 0.20/0.52  fof(f379,plain,(
% 0.20/0.52    $false | (~spl9_1 | ~spl9_13 | spl9_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f378,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.20/0.52  fof(f378,plain,(
% 0.20/0.52    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | (~spl9_1 | ~spl9_13 | spl9_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f322,f376])).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | (~spl9_1 | ~spl9_13)),
% 0.20/0.52    inference(resolution,[],[f375,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0) | (~spl9_1 | ~spl9_13)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f372])).
% 0.20/0.52  fof(f372,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | (~spl9_1 | ~spl9_13)),
% 0.20/0.52    inference(resolution,[],[f367,f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK2(k1_wellord2(sK1),X0),X0) | r1_tarski(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f103,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v3_ordinal1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r2_hidden(sK2(k1_wellord2(X0),X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f102,f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f79,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.52    inference(equality_resolution,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  % (20526)Refutation not found, incomplete strategy% (20526)------------------------------
% 0.20/0.52  % (20526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  % (20526)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20526)Memory used [KB]: 6140
% 0.20/0.52  % (20526)Time elapsed: 0.118 s
% 0.20/0.52  % (20526)------------------------------
% 0.20/0.52  % (20526)------------------------------
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(k1_wellord2(X0),X1),X1) | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f101,f39])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(sK2(k1_wellord2(X0),X1),X1) | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f42,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK2(X0,X1),X1) | r1_tarski(k3_relat_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),X1) | ? [X2] : (~r2_hidden(X2,X1) & r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0)))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : ((! [X1] : (r1_tarski(k3_relat_1(X0),X1) | ? [X2] : (~r2_hidden(X2,X1) & (r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0))))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : (! [X2] : ((r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0))) => r2_hidden(X2,X1)) => r1_tarski(k3_relat_1(X0),X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_wellord1)).
% 0.20/0.52  fof(f367,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK2(k1_wellord2(sK1),X1),sK0) | r1_tarski(sK1,X1)) ) | (~spl9_1 | ~spl9_13)),
% 0.20/0.52    inference(resolution,[],[f354,f191])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(sK1),X0),sK1) | r1_tarski(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f190,f35])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_tarski(X0,X1) | r2_hidden(sK2(k1_wellord2(X0),X1),X0)) )),
% 0.20/0.52    inference(resolution,[],[f189,f51])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_wellord1(k1_wellord2(X0)) | r2_hidden(sK2(k1_wellord2(X0),X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f188,f39])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f40,f89])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0) | r1_tarski(k3_relat_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f354,plain,(
% 0.20/0.52    ( ! [X4] : (~r2_hidden(X4,sK1) | r2_hidden(X4,sK0)) ) | (~spl9_1 | ~spl9_13)),
% 0.20/0.52    inference(forward_demodulation,[],[f350,f124])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl9_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f122])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl9_1 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    ( ! [X4] : (r2_hidden(X4,sK0) | ~r2_hidden(X4,k1_wellord1(k1_wellord2(sK0),sK1))) ) | ~spl9_13),
% 0.20/0.52    inference(resolution,[],[f261,f312])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    r2_hidden(sK1,sK0) | ~spl9_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f311])).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    spl9_13 <=> r2_hidden(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(X3,sK0) | r2_hidden(X2,sK0) | ~r2_hidden(X2,k1_wellord1(k1_wellord2(sK0),X3))) )),
% 0.20/0.52    inference(resolution,[],[f258,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    v3_ordinal1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f258,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (~v3_ordinal1(X4) | r2_hidden(X5,X4) | ~r2_hidden(X3,X4) | ~r2_hidden(X5,k1_wellord1(k1_wellord2(X4),X3))) )),
% 0.20/0.52    inference(resolution,[],[f256,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(X0,k1_wellord1(k1_wellord2(X2),X1))) )),
% 0.20/0.52    inference(resolution,[],[f74,f39])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0)) | ~r2_hidden(X1,X0) | r2_hidden(X2,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f255,f89])).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0)) | r2_hidden(X2,k3_relat_1(k1_wellord2(X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f254,f89])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0)) | r2_hidden(X2,k3_relat_1(k1_wellord2(X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f253,f39])).
% 0.20/0.52  fof(f253,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0)) | r2_hidden(X2,k3_relat_1(k1_wellord2(X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f92,f51])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X4,X3,X1] : (~v2_wellord1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X3,k3_relat_1(X1)) | ~r2_hidden(k4_tarski(X4,X3),X1) | r2_hidden(X4,k3_relat_1(X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f78,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X4,X3,X1] : (~v1_relat_1(X1) | ~v2_wellord1(X1) | ~r1_tarski(k3_relat_1(X1),k3_relat_1(X1)) | ~r2_hidden(X3,k3_relat_1(X1)) | ~r2_hidden(k4_tarski(X4,X3),X1) | r2_hidden(X4,k3_relat_1(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v2_wellord1(X1) | ~r1_tarski(X0,k3_relat_1(X1)) | ~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X4,X3),X1) | r2_hidden(X4,X0) | k3_relat_1(X1) != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 0.20/0.52    inference(rectify,[],[f4])).
% 0.20/0.53  % (20532)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | spl9_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f320])).
% 0.20/0.53  fof(f320,plain,(
% 0.20/0.53    spl9_15 <=> r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    spl9_2 | spl9_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f338])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    $false | (spl9_2 | spl9_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f337,f35])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    ~v3_ordinal1(sK1) | (spl9_2 | spl9_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f336,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    sK0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f336,plain,(
% 0.20/0.53    sK0 = sK1 | ~v3_ordinal1(sK1) | (spl9_2 | spl9_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f329,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~r2_hidden(sK0,sK1) | spl9_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    spl9_2 <=> r2_hidden(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.53  fof(f329,plain,(
% 0.20/0.53    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | spl9_13),
% 0.20/0.53    inference(resolution,[],[f313,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X1] : (r2_hidden(sK0,X1) | r2_hidden(X1,sK0) | sK0 = X1 | ~v3_ordinal1(X1)) )),
% 0.20/0.53    inference(resolution,[],[f53,f38])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.53  fof(f313,plain,(
% 0.20/0.53    ~r2_hidden(sK1,sK0) | spl9_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f311])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    ~spl9_13 | ~spl9_15 | ~spl9_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f318,f122,f320,f311])).
% 0.20/0.53  fof(f318,plain,(
% 0.20/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~spl9_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f308,f38])).
% 0.20/0.53  fof(f308,plain,(
% 0.20/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~spl9_1),
% 0.20/0.53    inference(superposition,[],[f212,f124])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f211,f89])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f210,f39])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f43,f51])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    ~spl9_2),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f285])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    $false | ~spl9_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f284,f98])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.20/0.54    inference(resolution,[],[f97,f36])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.20/0.54    inference(resolution,[],[f95,f39])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),X0)) )),
% 0.20/0.54    inference(resolution,[],[f44,f39])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~spl9_2),
% 0.20/0.54    inference(backward_demodulation,[],[f219,f282])).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl9_2),
% 0.20/0.54    inference(resolution,[],[f281,f69])).
% 0.20/0.54  fof(f281,plain,(
% 0.20/0.54    r1_tarski(sK0,sK1) | ~spl9_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f279,f192])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    ( ! [X1] : (r2_hidden(sK2(k1_wellord2(sK0),X1),sK0) | r1_tarski(sK0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f190,f38])).
% 0.20/0.54  fof(f279,plain,(
% 0.20/0.54    ~r2_hidden(sK2(k1_wellord2(sK0),sK1),sK0) | r1_tarski(sK0,sK1) | ~spl9_2),
% 0.20/0.54    inference(resolution,[],[f271,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(sK2(k1_wellord2(sK0),X1),X1) | r1_tarski(sK0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f103,f38])).
% 0.20/0.54  fof(f271,plain,(
% 0.20/0.54    ( ! [X2] : (r2_hidden(X2,sK1) | ~r2_hidden(X2,sK0)) ) | ~spl9_2),
% 0.20/0.54    inference(forward_demodulation,[],[f264,f148])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl9_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f147,f38])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl9_2),
% 0.20/0.54    inference(resolution,[],[f128,f106])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.20/0.54    inference(resolution,[],[f52,f35])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | ~spl9_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f126])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    ( ! [X2] : (r2_hidden(X2,sK1) | ~r2_hidden(X2,k1_wellord1(k1_wellord2(sK1),sK0))) ) | ~spl9_2),
% 0.20/0.54    inference(resolution,[],[f260,f128])).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_wellord1(k1_wellord2(sK1),X1))) )),
% 0.20/0.54    inference(resolution,[],[f258,f35])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~spl9_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f218,f35])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~v3_ordinal1(sK1) | ~spl9_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f217,f128])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~spl9_2),
% 0.20/0.54    inference(superposition,[],[f212,f148])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    spl9_1 | spl9_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f120,f126,f122])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f119,f35])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f118,f38])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f112,f37])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.54    inference(resolution,[],[f108,f107])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(sK0),X1) = X1) )),
% 0.20/0.54    inference(resolution,[],[f52,f38])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK1,X0) | r2_hidden(X0,sK1) | sK1 = X0 | ~v3_ordinal1(X0)) )),
% 0.20/0.54    inference(resolution,[],[f53,f35])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (20535)------------------------------
% 0.20/0.54  % (20535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20535)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (20535)Memory used [KB]: 10874
% 0.20/0.54  % (20535)Time elapsed: 0.071 s
% 0.20/0.54  % (20535)------------------------------
% 0.20/0.54  % (20535)------------------------------
% 0.20/0.54  % (20524)Refutation not found, incomplete strategy% (20524)------------------------------
% 0.20/0.54  % (20524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (20524)Memory used [KB]: 10746
% 0.20/0.54  % (20524)Time elapsed: 0.117 s
% 0.20/0.54  % (20524)------------------------------
% 0.20/0.54  % (20524)------------------------------
% 0.20/0.54  % (20512)Success in time 0.175 s
%------------------------------------------------------------------------------
