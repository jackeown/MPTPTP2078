%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 143 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  270 ( 443 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f67,f71,f79,f87,f91,f98,f126,f155,f188,f216,f243,f263,f276,f304])).

fof(f304,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_40
    | spl5_42 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_40
    | spl5_42 ),
    inference(subsumption_resolution,[],[f52,f302])).

fof(f302,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_4
    | ~ spl5_40
    | spl5_42 ),
    inference(forward_demodulation,[],[f301,f66])).

fof(f66,plain,
    ( ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_4
  <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f301,plain,
    ( ~ r2_hidden(k3_tarski(k1_zfmisc_1(sK2)),sK1)
    | ~ spl5_40
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f275,f262])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_tarski(X0),X1)
        | r1_setfam_1(X0,X1) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_40
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k3_tarski(X0),X1)
        | r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f275,plain,
    ( ~ r1_setfam_1(k1_zfmisc_1(sK2),sK1)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl5_42
  <=> r1_setfam_1(k1_zfmisc_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f52,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_1
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f276,plain,
    ( ~ spl5_42
    | spl5_2
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f244,f241,f55,f273])).

fof(f55,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f241,plain,
    ( spl5_37
  <=> ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_setfam_1(k1_zfmisc_1(X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f244,plain,
    ( ~ r1_setfam_1(k1_zfmisc_1(sK2),sK1)
    | spl5_2
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f57,f242])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r1_setfam_1(k1_zfmisc_1(X0),sK1)
        | r1_tarski(X0,sK0) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f241])).

fof(f57,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

% (8665)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f263,plain,
    ( spl5_40
    | ~ spl5_10
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f218,f214,f89,f261])).

fof(f89,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r1_setfam_1(X0,X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f214,plain,
    ( spl5_32
  <=> ! [X1,X0,X2] :
        ( r1_setfam_1(X0,X1)
        | ~ r2_hidden(k3_tarski(X2),X1)
        | ~ r2_hidden(sK3(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_tarski(X0),X1)
        | r1_setfam_1(X0,X1) )
    | ~ spl5_10
    | ~ spl5_32 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_tarski(X0),X1)
        | r1_setfam_1(X0,X1)
        | r1_setfam_1(X0,X1) )
    | ~ spl5_10
    | ~ spl5_32 ),
    inference(resolution,[],[f215,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_setfam_1(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r2_hidden(k3_tarski(X2),X1)
        | r1_setfam_1(X0,X1) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f243,plain,
    ( spl5_37
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f190,f186,f153,f69,f241])).

fof(f69,plain,
    ( spl5_5
  <=> ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f153,plain,
    ( spl5_22
  <=> ! [X0] :
        ( r1_setfam_1(X0,k1_tarski(sK0))
        | ~ r1_setfam_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f186,plain,
    ( spl5_27
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r1_setfam_1(k1_zfmisc_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f190,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_setfam_1(k1_zfmisc_1(X0),sK1) )
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f189,f70])).

fof(f70,plain,
    ( ! [X0] : k3_tarski(k1_tarski(X0)) = X0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f189,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k3_tarski(k1_tarski(sK0)))
        | ~ r1_setfam_1(k1_zfmisc_1(X0),sK1) )
    | ~ spl5_22
    | ~ spl5_27 ),
    inference(resolution,[],[f187,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( r1_setfam_1(X0,k1_tarski(sK0))
        | ~ r1_setfam_1(X0,sK1) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(k1_zfmisc_1(X0),X1)
        | r1_tarski(X0,k3_tarski(X1)) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f186])).

fof(f216,plain,
    ( spl5_32
    | ~ spl5_7
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f133,f124,f77,f214])).

fof(f77,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f124,plain,
    ( spl5_16
  <=> ! [X1,X3,X0] :
        ( r1_setfam_1(X0,X1)
        | ~ r1_tarski(sK3(X0,X1),X3)
        | ~ r2_hidden(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( r1_setfam_1(X0,X1)
        | ~ r2_hidden(k3_tarski(X2),X1)
        | ~ r2_hidden(sK3(X0,X1),X2) )
    | ~ spl5_7
    | ~ spl5_16 ),
    inference(resolution,[],[f125,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f125,plain,
    ( ! [X0,X3,X1] :
        ( ~ r1_tarski(sK3(X0,X1),X3)
        | r1_setfam_1(X0,X1)
        | ~ r2_hidden(X3,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f188,plain,
    ( spl5_27
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f105,f85,f65,f186])).

fof(f85,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r1_setfam_1(k1_zfmisc_1(X0),X1) )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(superposition,[],[f86,f66])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_setfam_1(X0,X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f155,plain,
    ( spl5_22
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f114,f96,f60,f153])).

fof(f60,plain,
    ( spl5_3
  <=> r1_setfam_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f96,plain,
    ( spl5_11
  <=> ! [X1,X0,X2] :
        ( r1_setfam_1(X0,X2)
        | ~ r1_setfam_1(X1,X2)
        | ~ r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f114,plain,
    ( ! [X0] :
        ( r1_setfam_1(X0,k1_tarski(sK0))
        | ~ r1_setfam_1(X0,sK1) )
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,
    ( r1_setfam_1(sK1,k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_setfam_1(X1,X2)
        | r1_setfam_1(X0,X2)
        | ~ r1_setfam_1(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f126,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f42,f124])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK3(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK4(X1,X4))
              & r2_hidden(sK4(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK4(X1,X4))
        & r2_hidden(sK4(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f98,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

fof(f91,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f79,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f71,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f67,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f63,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f58,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (8662)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (8670)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (8672)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (8662)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f307,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f53,f58,f63,f67,f71,f79,f87,f91,f98,f126,f155,f188,f216,f243,f263,f276,f304])).
% 0.21/0.46  fof(f304,plain,(
% 0.21/0.46    ~spl5_1 | ~spl5_4 | ~spl5_40 | spl5_42),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.46  fof(f303,plain,(
% 0.21/0.46    $false | (~spl5_1 | ~spl5_4 | ~spl5_40 | spl5_42)),
% 0.21/0.46    inference(subsumption_resolution,[],[f52,f302])).
% 0.21/0.46  fof(f302,plain,(
% 0.21/0.46    ~r2_hidden(sK2,sK1) | (~spl5_4 | ~spl5_40 | spl5_42)),
% 0.21/0.46    inference(forward_demodulation,[],[f301,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) ) | ~spl5_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl5_4 <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.46  fof(f301,plain,(
% 0.21/0.46    ~r2_hidden(k3_tarski(k1_zfmisc_1(sK2)),sK1) | (~spl5_40 | spl5_42)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f275,f262])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k3_tarski(X0),X1) | r1_setfam_1(X0,X1)) ) | ~spl5_40),
% 0.21/0.46    inference(avatar_component_clause,[],[f261])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    spl5_40 <=> ! [X1,X0] : (~r2_hidden(k3_tarski(X0),X1) | r1_setfam_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.46  fof(f275,plain,(
% 0.21/0.46    ~r1_setfam_1(k1_zfmisc_1(sK2),sK1) | spl5_42),
% 0.21/0.46    inference(avatar_component_clause,[],[f273])).
% 0.21/0.46  fof(f273,plain,(
% 0.21/0.46    spl5_42 <=> r1_setfam_1(k1_zfmisc_1(sK2),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    r2_hidden(sK2,sK1) | ~spl5_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl5_1 <=> r2_hidden(sK2,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.46  fof(f276,plain,(
% 0.21/0.46    ~spl5_42 | spl5_2 | ~spl5_37),
% 0.21/0.46    inference(avatar_split_clause,[],[f244,f241,f55,f273])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl5_2 <=> r1_tarski(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    spl5_37 <=> ! [X0] : (r1_tarski(X0,sK0) | ~r1_setfam_1(k1_zfmisc_1(X0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    ~r1_setfam_1(k1_zfmisc_1(sK2),sK1) | (spl5_2 | ~spl5_37)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f57,f242])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_setfam_1(k1_zfmisc_1(X0),sK1) | r1_tarski(X0,sK0)) ) | ~spl5_37),
% 0.21/0.46    inference(avatar_component_clause,[],[f241])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ~r1_tarski(sK2,sK0) | spl5_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  % (8665)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    spl5_40 | ~spl5_10 | ~spl5_32),
% 0.21/0.46    inference(avatar_split_clause,[],[f218,f214,f89,f261])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl5_10 <=> ! [X1,X0] : (r1_setfam_1(X0,X1) | r2_hidden(sK3(X0,X1),X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    spl5_32 <=> ! [X1,X0,X2] : (r1_setfam_1(X0,X1) | ~r2_hidden(k3_tarski(X2),X1) | ~r2_hidden(sK3(X0,X1),X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.46  fof(f218,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k3_tarski(X0),X1) | r1_setfam_1(X0,X1)) ) | (~spl5_10 | ~spl5_32)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f217])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k3_tarski(X0),X1) | r1_setfam_1(X0,X1) | r1_setfam_1(X0,X1)) ) | (~spl5_10 | ~spl5_32)),
% 0.21/0.46    inference(resolution,[],[f215,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_setfam_1(X0,X1)) ) | ~spl5_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r2_hidden(k3_tarski(X2),X1) | r1_setfam_1(X0,X1)) ) | ~spl5_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f214])).
% 0.21/0.46  fof(f243,plain,(
% 0.21/0.46    spl5_37 | ~spl5_5 | ~spl5_22 | ~spl5_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f190,f186,f153,f69,f241])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl5_5 <=> ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl5_22 <=> ! [X0] : (r1_setfam_1(X0,k1_tarski(sK0)) | ~r1_setfam_1(X0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    spl5_27 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r1_setfam_1(k1_zfmisc_1(X0),X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(X0,sK0) | ~r1_setfam_1(k1_zfmisc_1(X0),sK1)) ) | (~spl5_5 | ~spl5_22 | ~spl5_27)),
% 0.21/0.46    inference(forward_demodulation,[],[f189,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) ) | ~spl5_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(X0,k3_tarski(k1_tarski(sK0))) | ~r1_setfam_1(k1_zfmisc_1(X0),sK1)) ) | (~spl5_22 | ~spl5_27)),
% 0.21/0.46    inference(resolution,[],[f187,f154])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ( ! [X0] : (r1_setfam_1(X0,k1_tarski(sK0)) | ~r1_setfam_1(X0,sK1)) ) | ~spl5_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f153])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_setfam_1(k1_zfmisc_1(X0),X1) | r1_tarski(X0,k3_tarski(X1))) ) | ~spl5_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f186])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    spl5_32 | ~spl5_7 | ~spl5_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f133,f124,f77,f214])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl5_7 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    spl5_16 <=> ! [X1,X3,X0] : (r1_setfam_1(X0,X1) | ~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_setfam_1(X0,X1) | ~r2_hidden(k3_tarski(X2),X1) | ~r2_hidden(sK3(X0,X1),X2)) ) | (~spl5_7 | ~spl5_16)),
% 0.21/0.46    inference(resolution,[],[f125,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl5_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~r1_tarski(sK3(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) ) | ~spl5_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f124])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    spl5_27 | ~spl5_4 | ~spl5_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f105,f85,f65,f186])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl5_9 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r1_setfam_1(k1_zfmisc_1(X0),X1)) ) | (~spl5_4 | ~spl5_9)),
% 0.21/0.46    inference(superposition,[],[f86,f66])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) ) | ~spl5_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    spl5_22 | ~spl5_3 | ~spl5_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f114,f96,f60,f153])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl5_3 <=> r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl5_11 <=> ! [X1,X0,X2] : (r1_setfam_1(X0,X2) | ~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X0] : (r1_setfam_1(X0,k1_tarski(sK0)) | ~r1_setfam_1(X0,sK1)) ) | (~spl5_3 | ~spl5_11)),
% 0.21/0.46    inference(resolution,[],[f97,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    r1_setfam_1(sK1,k1_tarski(sK0)) | ~spl5_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_setfam_1(X1,X2) | r1_setfam_1(X0,X2) | ~r1_setfam_1(X0,X1)) ) | ~spl5_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    spl5_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f42,f124])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.46    inference(rectify,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl5_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_setfam_1(X0,X2) | ~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_setfam_1(X0,X2) | ~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_setfam_1(X0,X2) | (~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl5_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f89])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl5_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f85])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl5_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f77])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl5_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f69])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl5_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f65])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl5_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f60])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f14])).
% 0.21/0.46  fof(f14,conjecture,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ~spl5_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f55])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~r1_tarski(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl5_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f50])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    r2_hidden(sK2,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (8662)------------------------------
% 0.21/0.46  % (8662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8662)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (8662)Memory used [KB]: 6268
% 0.21/0.46  % (8662)Time elapsed: 0.052 s
% 0.21/0.46  % (8662)------------------------------
% 0.21/0.46  % (8662)------------------------------
% 0.21/0.47  % (8664)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (8656)Success in time 0.106 s
%------------------------------------------------------------------------------
