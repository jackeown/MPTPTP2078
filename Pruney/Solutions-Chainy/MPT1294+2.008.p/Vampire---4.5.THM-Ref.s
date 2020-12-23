%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 127 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 373 expanded)
%              Number of equality atoms :   62 ( 132 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f82,f124,f140,f144,f150,f155])).

fof(f155,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f152,f55])).

fof(f55,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_setfam_1(X1,X0)
        & k1_xboole_0 != X0 )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1 )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1 )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f152,plain,
    ( sP0(k1_xboole_0,sK4)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f60,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f60,plain,
    ( sP0(sK5,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> sP0(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f150,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f145,f74])).

fof(f74,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f145,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | spl7_2
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f63,f68,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k1_xboole_0 != k7_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f68,plain,
    ( k1_xboole_0 = k7_setfam_1(sK4,sK5)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_3
  <=> k1_xboole_0 = k7_setfam_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f63,plain,
    ( k1_xboole_0 != sK5
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f144,plain,
    ( spl7_3
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f141,f58,f67])).

fof(f141,plain,
    ( k1_xboole_0 = k7_setfam_1(sK4,sK5)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f140,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f130,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f130,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f123,f39,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP3(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP3(X1,X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f12,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X3,X0,X2] :
      ( sP1(X1,X3,X0,X2)
    <=> ( r2_hidden(X3,X2)
      <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( sP1(X1,X3,X0,X2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f123,plain,
    ( ~ sP3(k1_xboole_0,sK4,k1_xboole_0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_6
  <=> sP3(k1_xboole_0,sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f124,plain,
    ( ~ spl7_6
    | spl7_5 ),
    inference(avatar_split_clause,[],[f119,f79,f121])).

fof(f79,plain,
    ( spl7_5
  <=> k1_xboole_0 = k7_setfam_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

% (13482)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f119,plain,
    ( ~ sP3(k1_xboole_0,sK4,k1_xboole_0)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f81,f112,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X1,X0) = X2
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X0) = X2
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | k7_setfam_1(X1,X0) != X2 ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f112,plain,(
    ! [X0] : sP2(k1_xboole_0,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X2,sK6(X0,X1,X2),X1,X0)
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ sP1(X2,sK6(X0,X1,X2),X1,X0)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP1(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP1(X2,X3,X1,X0)
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ~ sP1(X2,sK6(X0,X1,X2),X1,X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ sP1(X2,X3,X1,X0)
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP1(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ sP1(X1,X3,X0,X2)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( sP1(X1,X3,X0,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f106,plain,(
    ! [X0,X1] : sP1(k1_xboole_0,X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f87,f87,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | r2_hidden(k3_subset_1(X2,X1),X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | r2_hidden(X1,X3) ) ) )
      & ( ( ( r2_hidden(X1,X3)
            | ~ r2_hidden(k3_subset_1(X2,X1),X0) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0,X2] :
      ( ( sP1(X1,X3,X0,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) ) ) )
      & ( ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X3,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

% (13492)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f81,plain,
    ( k1_xboole_0 != k7_setfam_1(sK4,k1_xboole_0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,
    ( ~ spl7_5
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f76,f67,f62,f79])).

fof(f76,plain,
    ( k1_xboole_0 != k7_setfam_1(sK4,k1_xboole_0)
    | ~ spl7_2
    | spl7_3 ),
    inference(backward_demodulation,[],[f69,f64])).

fof(f69,plain,
    ( k1_xboole_0 != k7_setfam_1(sK4,sK5)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f75,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ( k1_xboole_0 = sK5
        & k1_xboole_0 != k7_setfam_1(sK4,sK5) )
      | sP0(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
          | sP0(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK5
          & k1_xboole_0 != k7_setfam_1(sK4,sK5) )
        | sP0(sK5,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | sP0(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f9,f15])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

fof(f70,plain,
    ( spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f37,f67,f58])).

fof(f37,plain,
    ( k1_xboole_0 != k7_setfam_1(sK4,sK5)
    | sP0(sK5,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f38,f62,f58])).

fof(f38,plain,
    ( k1_xboole_0 = sK5
    | sP0(sK5,sK4) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13488)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (13480)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (13496)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (13499)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (13480)Refutation not found, incomplete strategy% (13480)------------------------------
% 0.21/0.49  % (13480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13480)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13480)Memory used [KB]: 6140
% 0.21/0.49  % (13480)Time elapsed: 0.059 s
% 0.21/0.49  % (13480)------------------------------
% 0.21/0.49  % (13480)------------------------------
% 0.21/0.49  % (13496)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f65,f70,f75,f82,f124,f140,f144,f150,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~spl7_1 | ~spl7_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    $false | (~spl7_1 | ~spl7_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X1,X0) & k1_xboole_0 != X0) | ~sP0(X0,X1))),
% 0.21/0.49    inference(rectify,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X1,X0] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) | ~sP0(X1,X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X1,X0] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) | ~sP0(X1,X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    sP0(k1_xboole_0,sK4) | (~spl7_1 | ~spl7_2)),
% 0.21/0.49    inference(backward_demodulation,[],[f60,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    k1_xboole_0 = sK5 | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl7_2 <=> k1_xboole_0 = sK5),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    sP0(sK5,sK4) | ~spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl7_1 <=> sP0(sK5,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl7_2 | ~spl7_3 | ~spl7_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    $false | (spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl7_4 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) | (spl7_2 | ~spl7_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f68,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k1_xboole_0 != k7_setfam_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    k1_xboole_0 = k7_setfam_1(sK4,sK5) | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl7_3 <=> k1_xboole_0 = k7_setfam_1(sK4,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    k1_xboole_0 != sK5 | spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl7_3 | ~spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f58,f67])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_xboole_0 = k7_setfam_1(sK4,sK5) | ~spl7_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f60,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k7_setfam_1(X1,X0) | ~sP0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl7_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    $false | spl7_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4))) | spl7_6),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f123,f39,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP3(X1,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (sP3(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(definition_folding,[],[f12,f19,f18,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X1,X3,X0,X2] : (sP1(X1,X3,X0,X2) <=> (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ! [X3] : (sP1(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X1,X0,X2] : ((k7_setfam_1(X0,X1) = X2 <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~sP3(k1_xboole_0,sK4,k1_xboole_0) | spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl7_6 <=> sP3(k1_xboole_0,sK4,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl7_6 | spl7_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f119,f79,f121])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl7_5 <=> k1_xboole_0 = k7_setfam_1(sK4,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  % (13482)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~sP3(k1_xboole_0,sK4,k1_xboole_0) | spl7_5),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f81,f112,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k7_setfam_1(X1,X0) = X2 | ~sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((k7_setfam_1(X1,X0) = X2 | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | k7_setfam_1(X1,X0) != X2)) | ~sP3(X0,X1,X2))),
% 0.21/0.49    inference(rectify,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X1,X0,X2] : (((k7_setfam_1(X0,X1) = X2 | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | k7_setfam_1(X0,X1) != X2)) | ~sP3(X1,X0,X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (sP2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f106,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP1(X2,sK6(X0,X1,X2),X1,X0) | sP2(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~sP1(X2,sK6(X0,X1,X2),X1,X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (sP1(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~sP1(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1))) => (~sP1(X2,sK6(X0,X1,X2),X1,X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~sP1(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (sP1(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~sP1(X1,X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (sP1(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP2(X2,X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP1(k1_xboole_0,X0,X1,k1_xboole_0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f87,f87,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3)) & (r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)))) & (((r2_hidden(X1,X3) | ~r2_hidden(k3_subset_1(X2,X1),X0)) & (r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(rectify,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X1,X3,X0,X2] : ((sP1(X1,X3,X0,X2) | ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)))) & (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~sP1(X1,X3,X0,X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f40,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.49  % (13492)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK4,k1_xboole_0) | spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl7_5 | ~spl7_2 | spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f67,f62,f79])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK4,k1_xboole_0) | (~spl7_2 | spl7_3)),
% 0.21/0.49    inference(backward_demodulation,[],[f69,f64])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK4,sK5) | spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f72])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ((k1_xboole_0 = sK5 & k1_xboole_0 != k7_setfam_1(sK4,sK5)) | sP0(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (((k1_xboole_0 = sK5 & k1_xboole_0 != k7_setfam_1(sK4,sK5)) | sP0(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(definition_folding,[],[f9,f15])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl7_1 | ~spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f67,f58])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK4,sK5) | sP0(sK5,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl7_1 | spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f62,f58])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    k1_xboole_0 = sK5 | sP0(sK5,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13496)------------------------------
% 0.21/0.49  % (13496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13496)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13496)Memory used [KB]: 10746
% 0.21/0.49  % (13496)Time elapsed: 0.070 s
% 0.21/0.49  % (13496)------------------------------
% 0.21/0.49  % (13496)------------------------------
% 0.21/0.49  % (13492)Refutation not found, incomplete strategy% (13492)------------------------------
% 0.21/0.49  % (13492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13479)Success in time 0.125 s
%------------------------------------------------------------------------------
