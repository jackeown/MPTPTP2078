%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 190 expanded)
%              Number of leaves         :   16 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  259 ( 723 expanded)
%              Number of equality atoms :   20 (  90 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f59,f123,f136,f187,f194,f203,f215])).

fof(f215,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f210,f24])).

fof(f24,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK3
            | ~ m1_subset_1(X5,sK1) )
        | ~ m1_subset_1(X4,sK0) )
    & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    & r2_hidden(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK3
              | ~ m1_subset_1(X5,sK1) )
          | ~ m1_subset_1(X4,sK0) )
      & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f210,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f207,f25])).

fof(f25,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f207,plain,
    ( ! [X14,X12,X13] :
        ( ~ r1_tarski(X12,k2_zfmisc_1(X13,X14))
        | ~ r2_hidden(sK3,X12) )
    | ~ spl7_5 ),
    inference(resolution,[],[f127,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK3,k2_zfmisc_1(X0,X1))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_5
  <=> ! [X1,X0] : ~ r2_hidden(sK3,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f203,plain,
    ( ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(resolution,[],[f197,f130])).

fof(f130,plain,
    ( r2_hidden(sK6(sK3),sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_6
  <=> r2_hidden(sK6(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

% (1252)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f197,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f46,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl7_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f194,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl7_7 ),
    inference(resolution,[],[f189,f24])).

fof(f189,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl7_7 ),
    inference(resolution,[],[f180,f25])).

fof(f180,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(X9,k2_zfmisc_1(sK0,X10))
        | ~ r2_hidden(sK3,X9) )
    | spl7_7 ),
    inference(resolution,[],[f175,f31])).

fof(f175,plain,
    ( ! [X0] : ~ r2_hidden(sK3,k2_zfmisc_1(sK0,X0))
    | spl7_7 ),
    inference(condensation,[],[f174])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3,k2_zfmisc_1(sK0,X0))
        | ~ r2_hidden(sK3,k2_zfmisc_1(X1,X2)) )
    | spl7_7 ),
    inference(superposition,[],[f141,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

% (1240)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f141,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(sK5(sK3),X2),k2_zfmisc_1(sK0,X3))
    | spl7_7 ),
    inference(resolution,[],[f135,f36])).

% (1249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f135,plain,
    ( ~ r2_hidden(sK5(sK3),sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_7
  <=> r2_hidden(sK5(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

% (1241)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f187,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f182,f24])).

fof(f182,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl7_6 ),
    inference(resolution,[],[f156,f25])).

fof(f156,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(X9,k2_zfmisc_1(X10,sK1))
        | ~ r2_hidden(sK3,X9) )
    | spl7_6 ),
    inference(resolution,[],[f151,f31])).

fof(f151,plain,
    ( ! [X0] : ~ r2_hidden(sK3,k2_zfmisc_1(X0,sK1))
    | spl7_6 ),
    inference(condensation,[],[f150])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3,k2_zfmisc_1(X0,sK1))
        | ~ r2_hidden(sK3,k2_zfmisc_1(X1,X2)) )
    | spl7_6 ),
    inference(superposition,[],[f137,f35])).

fof(f137,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK6(sK3)),k2_zfmisc_1(X1,sK1))
    | spl7_6 ),
    inference(resolution,[],[f131,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,
    ( ~ r2_hidden(sK6(sK3),sK1)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f136,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f124,f57,f133,f129,f126])).

fof(f57,plain,
    ( spl7_4
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK6(X0),sK1)
        | ~ r2_hidden(sK5(X0),sK0)
        | sK3 != X0
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK3),sK0)
        | ~ r2_hidden(sK6(sK3),sK1)
        | ~ r2_hidden(sK3,k2_zfmisc_1(X0,X1)) )
    | ~ spl7_4 ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( sK3 != X0
        | ~ r2_hidden(sK5(X0),sK0)
        | ~ r2_hidden(sK6(X0),sK1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f123,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f113,f24])).

fof(f113,plain,
    ( ! [X8] : ~ r2_hidden(X8,sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f100,f25])).

fof(f100,plain,
    ( ! [X14,X12,X13] :
        ( ~ r1_tarski(X13,k2_zfmisc_1(sK0,X14))
        | ~ r2_hidden(X12,X13) )
    | ~ spl7_3 ),
    inference(resolution,[],[f95,f31])).

fof(f95,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,X1))
    | ~ spl7_3 ),
    inference(condensation,[],[f94])).

fof(f94,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) )
    | ~ spl7_3 ),
    inference(superposition,[],[f65,f35])).

fof(f65,plain,
    ( ! [X4,X5,X3] : ~ r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(sK0,X5))
    | ~ spl7_3 ),
    inference(resolution,[],[f63,f36])).

fof(f63,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f55,f34])).

fof(f55,plain,
    ( v1_xboole_0(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f59,plain,
    ( spl7_3
    | spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f51,f48,f57,f53])).

fof(f48,plain,
    ( spl7_2
  <=> ! [X1,X0,X2] :
        ( sK3 != X0
        | ~ r2_hidden(sK6(X0),sK1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(sK5(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK6(X0),sK1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | sK3 != X0
        | ~ r2_hidden(sK5(X0),sK0)
        | v1_xboole_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(X0),sK0)
        | ~ r2_hidden(sK6(X0),sK1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | sK3 != X0 )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f42,f48,f44])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sK3 != X0
      | ~ m1_subset_1(sK5(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK6(X0),sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0),sK1)
      | sK3 != X0
      | ~ m1_subset_1(sK5(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(superposition,[],[f26,f35])).

fof(f26,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (1251)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (1236)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (1238)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (1246)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (1228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (1239)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (1225)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (1236)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (1229)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (1226)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (1230)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (1226)Refutation not found, incomplete strategy% (1226)------------------------------
% 0.22/0.54  % (1226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1226)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1226)Memory used [KB]: 10618
% 0.22/0.54  % (1226)Time elapsed: 0.123 s
% 0.22/0.54  % (1226)------------------------------
% 0.22/0.54  % (1226)------------------------------
% 0.22/0.54  % (1224)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (1227)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (1253)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (1250)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f50,f59,f123,f136,f187,f194,f203,f215])).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ~spl7_5),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    $false | ~spl7_5),
% 0.22/0.55    inference(resolution,[],[f210,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    r2_hidden(sK3,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2)) => (! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.22/0.55    inference(negated_conjecture,[],[f6])).
% 0.22/0.55  fof(f6,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    ~r2_hidden(sK3,sK2) | ~spl7_5),
% 0.22/0.55    inference(resolution,[],[f207,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    ( ! [X14,X12,X13] : (~r1_tarski(X12,k2_zfmisc_1(X13,X14)) | ~r2_hidden(sK3,X12)) ) | ~spl7_5),
% 0.22/0.55    inference(resolution,[],[f127,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK3,k2_zfmisc_1(X0,X1))) ) | ~spl7_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    spl7_5 <=> ! [X1,X0] : ~r2_hidden(sK3,k2_zfmisc_1(X0,X1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.55  fof(f202,plain,(
% 0.22/0.55    $false | (~spl7_1 | ~spl7_6)),
% 0.22/0.55    inference(resolution,[],[f197,f130])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    r2_hidden(sK6(sK3),sK1) | ~spl7_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f129])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    spl7_6 <=> r2_hidden(sK6(sK3),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.55  % (1252)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl7_1),
% 0.22/0.55    inference(resolution,[],[f46,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | ~spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    spl7_1 <=> v1_xboole_0(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    spl7_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f190])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    $false | spl7_7),
% 0.22/0.55    inference(resolution,[],[f189,f24])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    ~r2_hidden(sK3,sK2) | spl7_7),
% 0.22/0.55    inference(resolution,[],[f180,f25])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    ( ! [X10,X9] : (~r1_tarski(X9,k2_zfmisc_1(sK0,X10)) | ~r2_hidden(sK3,X9)) ) | spl7_7),
% 0.22/0.55    inference(resolution,[],[f175,f31])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK3,k2_zfmisc_1(sK0,X0))) ) | spl7_7),
% 0.22/0.55    inference(condensation,[],[f174])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK3,k2_zfmisc_1(sK0,X0)) | ~r2_hidden(sK3,k2_zfmisc_1(X1,X2))) ) | spl7_7),
% 0.22/0.55    inference(superposition,[],[f141,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK5(X0),sK6(X0)) = X0)),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  % (1240)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK5(sK3),X2),k2_zfmisc_1(sK0,X3))) ) | spl7_7),
% 0.22/0.55    inference(resolution,[],[f135,f36])).
% 0.22/0.55  % (1249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.55    inference(nnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ~r2_hidden(sK5(sK3),sK0) | spl7_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f133])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    spl7_7 <=> r2_hidden(sK5(sK3),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.55  % (1241)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    spl7_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f183])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    $false | spl7_6),
% 0.22/0.55    inference(resolution,[],[f182,f24])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    ~r2_hidden(sK3,sK2) | spl7_6),
% 0.22/0.55    inference(resolution,[],[f156,f25])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X10,X9] : (~r1_tarski(X9,k2_zfmisc_1(X10,sK1)) | ~r2_hidden(sK3,X9)) ) | spl7_6),
% 0.22/0.55    inference(resolution,[],[f151,f31])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK3,k2_zfmisc_1(X0,sK1))) ) | spl7_6),
% 0.22/0.55    inference(condensation,[],[f150])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK3,k2_zfmisc_1(X0,sK1)) | ~r2_hidden(sK3,k2_zfmisc_1(X1,X2))) ) | spl7_6),
% 0.22/0.55    inference(superposition,[],[f137,f35])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK6(sK3)),k2_zfmisc_1(X1,sK1))) ) | spl7_6),
% 0.22/0.55    inference(resolution,[],[f131,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ~r2_hidden(sK6(sK3),sK1) | spl7_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f129])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f124,f57,f133,f129,f126])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    spl7_4 <=> ! [X1,X0,X2] : (~r2_hidden(sK6(X0),sK1) | ~r2_hidden(sK5(X0),sK0) | sK3 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(sK3),sK0) | ~r2_hidden(sK6(sK3),sK1) | ~r2_hidden(sK3,k2_zfmisc_1(X0,X1))) ) | ~spl7_4),
% 0.22/0.55    inference(equality_resolution,[],[f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (sK3 != X0 | ~r2_hidden(sK5(X0),sK0) | ~r2_hidden(sK6(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) ) | ~spl7_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f57])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    ~spl7_3),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f121])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    $false | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f113,f24])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    ( ! [X8] : (~r2_hidden(X8,sK2)) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f100,f25])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X14,X12,X13] : (~r1_tarski(X13,k2_zfmisc_1(sK0,X14)) | ~r2_hidden(X12,X13)) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f95,f31])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK0,X1))) ) | ~spl7_3),
% 0.22/0.55    inference(condensation,[],[f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK0,X1)) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) ) | ~spl7_3),
% 0.22/0.55    inference(superposition,[],[f65,f35])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(sK0,X5))) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f63,f36])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f55,f34])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    v1_xboole_0(sK0) | ~spl7_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    spl7_3 <=> v1_xboole_0(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    spl7_3 | spl7_4 | ~spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f51,f48,f57,f53])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    spl7_2 <=> ! [X1,X0,X2] : (sK3 != X0 | ~r2_hidden(sK6(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(sK5(X0),sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sK3 != X0 | ~r2_hidden(sK5(X0),sK0) | v1_xboole_0(sK0)) ) | ~spl7_2),
% 0.22/0.55    inference(resolution,[],[f49,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(nnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0),sK0) | ~r2_hidden(sK6(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sK3 != X0) ) | ~spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f48])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    spl7_1 | spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f42,f48,f44])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (sK3 != X0 | ~m1_subset_1(sK5(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK6(X0),sK1) | v1_xboole_0(sK1)) )),
% 0.22/0.55    inference(resolution,[],[f41,f28])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0),sK1) | sK3 != X0 | ~m1_subset_1(sK5(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.55    inference(superposition,[],[f26,f35])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (1236)------------------------------
% 0.22/0.55  % (1236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1236)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (1236)Memory used [KB]: 6268
% 0.22/0.55  % (1236)Time elapsed: 0.123 s
% 0.22/0.55  % (1236)------------------------------
% 0.22/0.55  % (1236)------------------------------
% 0.22/0.55  % (1219)Success in time 0.186 s
%------------------------------------------------------------------------------
