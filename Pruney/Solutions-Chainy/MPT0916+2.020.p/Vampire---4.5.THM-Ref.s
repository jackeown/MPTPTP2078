%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 390 expanded)
%              Number of leaves         :   21 ( 113 expanded)
%              Depth                    :   14
%              Number of atoms          :  313 (1305 expanded)
%              Number of equality atoms :   60 ( 133 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f542,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f128,f142,f163,f179,f188,f240,f253,f288,f338,f458,f490,f541])).

% (20722)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f541,plain,
    ( ~ spl8_5
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f294,f39,f505,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

% (20710)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (20709)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (20713)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (20708)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (20701)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (20714)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (20719)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (20718)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f505,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f174,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f174,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_10
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f294,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f89,f119])).

fof(f89,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f26,f86,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f86,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(unit_resulting_resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f56,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f42,f31])).

fof(f42,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f490,plain,
    ( spl8_2
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | spl8_2
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f56,f479,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f479,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl8_2
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(backward_demodulation,[],[f78,f474])).

fof(f474,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f126,f118,f122,f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f43,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f22,f36])).

fof(f22,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,
    ( k1_xboole_0 != sK2
    | spl8_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f118,plain,
    ( k1_xboole_0 != sK0
    | spl8_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f126,plain,
    ( k1_xboole_0 != sK1
    | spl8_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f78,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f458,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f345,f348,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f348,plain,
    ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f104,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f104,plain,(
    r2_hidden(sK7(sK1,k1_xboole_0),sK1) ),
    inference(unit_resulting_resolution,[],[f101,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f100,f40])).

fof(f100,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f25,f87,f30])).

fof(f87,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(unit_resulting_resolution,[],[f56,f32])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f345,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f101,f127])).

fof(f338,plain,
    ( ~ spl8_5
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl8_5
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f39,f305,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f305,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | spl8_11 ),
    inference(backward_demodulation,[],[f178,f119])).

fof(f178,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_11
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f288,plain,
    ( spl8_3
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl8_3
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f56,f254,f31])).

fof(f254,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl8_3
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f82,f187])).

fof(f187,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_12
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f82,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl8_3
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f253,plain,
    ( ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f193,f39,f242,f40])).

fof(f242,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f158,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f158,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_8
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f193,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f62,f123])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f24,f57,f30])).

fof(f57,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(unit_resulting_resolution,[],[f42,f32])).

fof(f24,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f240,plain,
    ( ~ spl8_6
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl8_6
    | spl8_9 ),
    inference(unit_resulting_resolution,[],[f39,f204,f41])).

fof(f204,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_6
    | spl8_9 ),
    inference(backward_demodulation,[],[f162,f123])).

fof(f162,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_9
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f188,plain,
    ( spl8_12
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f58,f125,f121,f117,f185])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f179,plain,
    ( spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f170,f176,f172])).

fof(f170,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f149,f35])).

fof(f149,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0),sK0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f91,f34])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f89,f40])).

fof(f163,plain,
    ( spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f154,f160,f156])).

fof(f154,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f147,f35])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK2,X0),sK2)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f64,f34])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f62,f40])).

fof(f142,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f42,f131,f32])).

fof(f131,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl8_1
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f74,f115])).

fof(f115,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_4
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f74,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_1
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f128,plain,
    ( spl8_4
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f60,f125,f121,f117,f113])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f21,f80,f76,f72])).

fof(f21,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (20700)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (20695)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (20711)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (20715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (20707)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (20698)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (20704)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (20704)Refutation not found, incomplete strategy% (20704)------------------------------
% 0.21/0.51  % (20704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20704)Memory used [KB]: 10746
% 0.21/0.51  % (20704)Time elapsed: 0.107 s
% 0.21/0.51  % (20704)------------------------------
% 0.21/0.51  % (20704)------------------------------
% 0.21/0.51  % (20697)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20693)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (20696)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (20703)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (20703)Refutation not found, incomplete strategy% (20703)------------------------------
% 0.21/0.52  % (20703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20703)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20703)Memory used [KB]: 10746
% 0.21/0.52  % (20703)Time elapsed: 0.117 s
% 0.21/0.52  % (20703)------------------------------
% 0.21/0.52  % (20703)------------------------------
% 0.21/0.53  % (20717)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (20712)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (20694)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (20705)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (20716)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (20706)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (20720)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (20721)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (20699)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (20702)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20697)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f542,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f83,f128,f142,f163,f179,f188,f240,f253,f288,f338,f458,f490,f541])).
% 0.21/0.54  % (20722)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  fof(f541,plain,(
% 0.21/0.54    ~spl8_5 | ~spl8_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f535])).
% 0.21/0.54  fof(f535,plain,(
% 0.21/0.54    $false | (~spl8_5 | ~spl8_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f294,f39,f505,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.54  % (20710)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (20709)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (20713)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20708)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (20701)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (20714)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (20719)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (20718)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  fof(f505,plain,(
% 0.21/0.56    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_5 | ~spl8_10)),
% 0.21/0.56    inference(backward_demodulation,[],[f174,f119])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | ~spl8_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl8_5 <=> k1_xboole_0 = sK0),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    r1_tarski(sK0,sK0) | ~spl8_10),
% 0.21/0.56    inference(avatar_component_clause,[],[f172])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    spl8_10 <=> r1_tarski(sK0,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl8_5),
% 0.21/0.56    inference(backward_demodulation,[],[f89,f119])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ~v1_xboole_0(sK0)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f26,f86,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f56,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f42,f31])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.56    inference(definition_unfolding,[],[f23,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(flattening,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f490,plain,(
% 0.21/0.56    spl8_2 | spl8_5 | spl8_6 | spl8_7),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f482])).
% 0.21/0.56  fof(f482,plain,(
% 0.21/0.56    $false | (spl8_2 | spl8_5 | spl8_6 | spl8_7)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f56,f479,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f479,plain,(
% 0.21/0.56    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl8_2 | spl8_5 | spl8_6 | spl8_7)),
% 0.21/0.56    inference(backward_demodulation,[],[f78,f474])).
% 0.21/0.56  fof(f474,plain,(
% 0.21/0.56    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | (spl8_5 | spl8_6 | spl8_7)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f126,f118,f122,f43,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f28,f36])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.56    inference(definition_unfolding,[],[f22,f36])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    k1_xboole_0 != sK2 | spl8_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f121])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl8_6 <=> k1_xboole_0 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | spl8_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | spl8_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f125])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    spl8_7 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl8_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    spl8_2 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.56  fof(f458,plain,(
% 0.21/0.56    ~spl8_7),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f455])).
% 0.21/0.56  fof(f455,plain,(
% 0.21/0.56    $false | ~spl8_7),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f345,f348,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f348,plain,(
% 0.21/0.56    r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl8_7),
% 0.21/0.56    inference(backward_demodulation,[],[f104,f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~spl8_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f125])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    r2_hidden(sK7(sK1,k1_xboole_0),sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f101,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ~r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f39,f100,f40])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ~v1_xboole_0(sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f25,f87,f30])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f56,f32])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f345,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl8_7),
% 0.21/0.56    inference(backward_demodulation,[],[f101,f127])).
% 0.21/0.56  fof(f338,plain,(
% 0.21/0.56    ~spl8_5 | spl8_11),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f333])).
% 0.21/0.56  fof(f333,plain,(
% 0.21/0.56    $false | (~spl8_5 | spl8_11)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f39,f305,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.56  fof(f305,plain,(
% 0.21/0.56    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl8_5 | spl8_11)),
% 0.21/0.56    inference(backward_demodulation,[],[f178,f119])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,sK0) | spl8_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f176])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    spl8_11 <=> r1_xboole_0(sK0,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.56  fof(f288,plain,(
% 0.21/0.56    spl8_3 | ~spl8_12),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    $false | (spl8_3 | ~spl8_12)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f56,f254,f31])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (spl8_3 | ~spl8_12)),
% 0.21/0.56    inference(backward_demodulation,[],[f82,f187])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl8_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f185])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    spl8_12 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl8_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    spl8_3 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    ~spl8_6 | ~spl8_8),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    $false | (~spl8_6 | ~spl8_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f193,f39,f242,f40])).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_6 | ~spl8_8)),
% 0.21/0.56    inference(forward_demodulation,[],[f158,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~spl8_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f121])).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    r1_tarski(sK2,sK2) | ~spl8_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    spl8_8 <=> r1_tarski(sK2,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl8_6),
% 0.21/0.56    inference(backward_demodulation,[],[f62,f123])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ~v1_xboole_0(sK2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f24,f57,f30])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f42,f32])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    ~spl8_6 | spl8_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    $false | (~spl8_6 | spl8_9)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f39,f204,f41])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl8_6 | spl8_9)),
% 0.21/0.56    inference(backward_demodulation,[],[f162,f123])).
% 0.21/0.56  fof(f162,plain,(
% 0.21/0.56    ~r1_xboole_0(sK2,sK2) | spl8_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f160])).
% 0.21/0.56  fof(f160,plain,(
% 0.21/0.56    spl8_9 <=> r1_xboole_0(sK2,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    spl8_12 | spl8_5 | spl8_6 | spl8_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f58,f125,f121,f117,f185])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.21/0.56    inference(resolution,[],[f43,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f27,f36])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    spl8_10 | ~spl8_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f170,f176,f172])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,sK0) | r1_tarski(sK0,sK0)),
% 0.21/0.56    inference(resolution,[],[f149,f35])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(sK0,X0),sK0) | ~r1_xboole_0(sK0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f91,f34])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_xboole_0(sK0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f89,f40])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    spl8_8 | ~spl8_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f154,f160,f156])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    ~r1_xboole_0(sK2,sK2) | r1_tarski(sK2,sK2)),
% 0.21/0.56    inference(resolution,[],[f147,f35])).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(sK2,X0),sK2) | ~r1_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f64,f34])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f62,f40])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    spl8_1 | ~spl8_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    $false | (spl8_1 | ~spl8_4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f42,f131,f32])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl8_1 | ~spl8_4)),
% 0.21/0.56    inference(backward_demodulation,[],[f74,f115])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl8_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f113])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    spl8_4 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl8_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    spl8_1 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    spl8_4 | spl8_5 | spl8_6 | spl8_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f60,f125,f121,f117,f113])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.21/0.56    inference(resolution,[],[f43,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f29,f36])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f21,f80,f76,f72])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20697)------------------------------
% 0.21/0.56  % (20697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20697)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20697)Memory used [KB]: 6396
% 0.21/0.56  % (20697)Time elapsed: 0.141 s
% 0.21/0.56  % (20697)------------------------------
% 0.21/0.56  % (20697)------------------------------
% 0.21/0.56  % (20689)Success in time 0.201 s
%------------------------------------------------------------------------------
