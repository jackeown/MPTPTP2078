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
% DateTime   : Thu Dec  3 12:43:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 163 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  266 ( 498 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f390,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f111,f117,f133,f160,f210,f289,f315,f360,f378,f388])).

fof(f388,plain,
    ( ~ spl5_13
    | ~ spl5_45 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f383,f116])).

fof(f116,plain,
    ( r2_xboole_0(sK2,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_13
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f383,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl5_45 ),
    inference(resolution,[],[f377,f35])).

% (11076)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f377,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl5_45
  <=> r2_hidden(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f378,plain,
    ( spl5_45
    | ~ spl5_22
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f369,f358,f158,f376])).

fof(f158,plain,
    ( spl5_22
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f358,plain,
    ( spl5_43
  <=> m1_subset_1(sK4(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f369,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | ~ spl5_22
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f365,f159])).

fof(f159,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f158])).

fof(f365,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl5_43 ),
    inference(resolution,[],[f359,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f359,plain,
    ( m1_subset_1(sK4(sK2,sK1),sK0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f358])).

fof(f360,plain,
    ( spl5_43
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f232,f208,f358])).

fof(f208,plain,
    ( spl5_28
  <=> r2_hidden(sK4(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f232,plain,
    ( m1_subset_1(sK4(sK2,sK1),sK0)
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f231,f230])).

fof(f230,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_28 ),
    inference(resolution,[],[f209,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f209,plain,
    ( r2_hidden(sK4(sK2,sK1),sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f231,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(sK4(sK2,sK1),sK0)
    | ~ spl5_28 ),
    inference(resolution,[],[f209,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f315,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f313,f287,f46,f42,f106])).

fof(f106,plain,
    ( spl5_11
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f42,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f46,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f287,plain,
    ( spl5_37
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f313,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f312,f43])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f308,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f308,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ spl5_37 ),
    inference(resolution,[],[f288,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f288,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f287])).

fof(f289,plain,
    ( spl5_37
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f161,f131,f109,f287])).

fof(f109,plain,
    ( spl5_12
  <=> m1_subset_1(sK3(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f131,plain,
    ( spl5_16
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f161,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f119,f132])).

fof(f132,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f119,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f110,f20])).

fof(f20,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f210,plain,
    ( spl5_28
    | ~ spl5_3
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f199,f158,f46,f208])).

fof(f199,plain,
    ( r2_hidden(sK4(sK2,sK1),sK0)
    | ~ spl5_3
    | ~ spl5_22 ),
    inference(resolution,[],[f159,f56])).

fof(f56,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f160,plain,
    ( spl5_22
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f135,f115,f158])).

fof(f135,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f116,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,
    ( spl5_11
    | spl5_16
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f92,f46,f42,f131,f106])).

fof(f92,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r1_tarski(sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f50,f47])).

fof(f50,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(sK3(sK0,sK2,X1),sK2)
        | r1_tarski(sK2,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f117,plain,
    ( spl5_13
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f113,f106,f38,f115])).

fof(f38,plain,
    ( spl5_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,
    ( r2_xboole_0(sK2,sK1)
    | spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f112,f39])).

fof(f39,plain,
    ( sK1 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f112,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK2,sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f107,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f107,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f111,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f90,f46,f42,f109,f106])).

fof(f90,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),sK0)
    | r1_tarski(sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f49,f47])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | m1_subset_1(sK3(sK0,sK2,X0),sK0)
        | r1_tarski(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11072)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (11078)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (11060)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (11063)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (11079)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.47  % (11060)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f390,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f40,f44,f48,f111,f117,f133,f160,f210,f289,f315,f360,f378,f388])).
% 0.20/0.48  fof(f388,plain,(
% 0.20/0.48    ~spl5_13 | ~spl5_45),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f387])).
% 0.20/0.48  fof(f387,plain,(
% 0.20/0.48    $false | (~spl5_13 | ~spl5_45)),
% 0.20/0.48    inference(subsumption_resolution,[],[f383,f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    r2_xboole_0(sK2,sK1) | ~spl5_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl5_13 <=> r2_xboole_0(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.48  fof(f383,plain,(
% 0.20/0.48    ~r2_xboole_0(sK2,sK1) | ~spl5_45),
% 0.20/0.48    inference(resolution,[],[f377,f35])).
% 0.20/0.48  % (11076)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.48  fof(f377,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK2) | ~spl5_45),
% 0.20/0.48    inference(avatar_component_clause,[],[f376])).
% 0.20/0.48  fof(f376,plain,(
% 0.20/0.48    spl5_45 <=> r2_hidden(sK4(sK2,sK1),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.20/0.48  fof(f378,plain,(
% 0.20/0.48    spl5_45 | ~spl5_22 | ~spl5_43),
% 0.20/0.48    inference(avatar_split_clause,[],[f369,f358,f158,f376])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    spl5_22 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.48  fof(f358,plain,(
% 0.20/0.48    spl5_43 <=> m1_subset_1(sK4(sK2,sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.20/0.48  fof(f369,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK2) | (~spl5_22 | ~spl5_43)),
% 0.20/0.48    inference(subsumption_resolution,[],[f365,f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK1) | ~spl5_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f158])).
% 0.20/0.48  fof(f365,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK2) | ~r2_hidden(sK4(sK2,sK1),sK1) | ~spl5_43),
% 0.20/0.48    inference(resolution,[],[f359,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.48  fof(f359,plain,(
% 0.20/0.48    m1_subset_1(sK4(sK2,sK1),sK0) | ~spl5_43),
% 0.20/0.48    inference(avatar_component_clause,[],[f358])).
% 0.20/0.48  fof(f360,plain,(
% 0.20/0.48    spl5_43 | ~spl5_28),
% 0.20/0.48    inference(avatar_split_clause,[],[f232,f208,f358])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    spl5_28 <=> r2_hidden(sK4(sK2,sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    m1_subset_1(sK4(sK2,sK1),sK0) | ~spl5_28),
% 0.20/0.48    inference(subsumption_resolution,[],[f231,f230])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0) | ~spl5_28),
% 0.20/0.48    inference(resolution,[],[f209,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK0) | ~spl5_28),
% 0.20/0.48    inference(avatar_component_clause,[],[f208])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | m1_subset_1(sK4(sK2,sK1),sK0) | ~spl5_28),
% 0.20/0.48    inference(resolution,[],[f209,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    spl5_11 | ~spl5_2 | ~spl5_3 | ~spl5_37),
% 0.20/0.48    inference(avatar_split_clause,[],[f313,f287,f46,f42,f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl5_11 <=> r1_tarski(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    spl5_37 <=> r2_hidden(sK3(sK0,sK2,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.48  fof(f313,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_37)),
% 0.20/0.48    inference(subsumption_resolution,[],[f312,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f312,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | (~spl5_3 | ~spl5_37)),
% 0.20/0.48    inference(subsumption_resolution,[],[f308,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f46])).
% 0.20/0.48  fof(f308,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | ~spl5_37),
% 0.20/0.48    inference(resolution,[],[f288,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f288,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK2,sK1),sK1) | ~spl5_37),
% 0.20/0.48    inference(avatar_component_clause,[],[f287])).
% 0.20/0.48  fof(f289,plain,(
% 0.20/0.48    spl5_37 | ~spl5_12 | ~spl5_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f161,f131,f109,f287])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl5_12 <=> m1_subset_1(sK3(sK0,sK2,sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    spl5_16 <=> r2_hidden(sK3(sK0,sK2,sK1),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK2,sK1),sK1) | (~spl5_12 | ~spl5_16)),
% 0.20/0.48    inference(subsumption_resolution,[],[f119,f132])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK2,sK1),sK2) | ~spl5_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f131])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | r2_hidden(sK3(sK0,sK2,sK1),sK1) | ~spl5_12),
% 0.20/0.48    inference(resolution,[],[f110,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0,sK2,sK1),sK0) | ~spl5_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f109])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    spl5_28 | ~spl5_3 | ~spl5_22),
% 0.20/0.48    inference(avatar_split_clause,[],[f199,f158,f46,f208])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK0) | (~spl5_3 | ~spl5_22)),
% 0.20/0.48    inference(resolution,[],[f159,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) ) | ~spl5_3),
% 0.20/0.48    inference(resolution,[],[f47,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl5_22 | ~spl5_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f135,f115,f158])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK1),sK1) | ~spl5_13),
% 0.20/0.48    inference(resolution,[],[f116,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl5_11 | spl5_16 | ~spl5_2 | ~spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f92,f46,f42,f131,f106])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK2,sK1),sK2) | r1_tarski(sK2,sK1) | (~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(resolution,[],[f50,f47])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK0,sK2,X1),sK2) | r1_tarski(sK2,X1)) ) | ~spl5_2),
% 0.20/0.48    inference(resolution,[],[f43,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl5_13 | spl5_1 | ~spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f113,f106,f38,f115])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    spl5_1 <=> sK1 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    r2_xboole_0(sK2,sK1) | (spl5_1 | ~spl5_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    sK1 != sK2 | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f38])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    sK1 = sK2 | r2_xboole_0(sK2,sK1) | ~spl5_11),
% 0.20/0.48    inference(resolution,[],[f107,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~spl5_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl5_11 | spl5_12 | ~spl5_2 | ~spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f90,f46,f42,f109,f106])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0,sK2,sK1),sK0) | r1_tarski(sK2,sK1) | (~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(resolution,[],[f49,f47])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | m1_subset_1(sK3(sK0,sK2,X0),sK0) | r1_tarski(sK2,X0)) ) | ~spl5_2),
% 0.20/0.48    inference(resolution,[],[f43,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f46])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f42])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f38])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    sK1 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (11060)------------------------------
% 0.20/0.48  % (11060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11060)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (11060)Memory used [KB]: 6396
% 0.20/0.48  % (11060)Time elapsed: 0.059 s
% 0.20/0.48  % (11060)------------------------------
% 0.20/0.48  % (11060)------------------------------
% 0.20/0.48  % (11059)Success in time 0.129 s
%------------------------------------------------------------------------------
