%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1715+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 303 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  262 (1821 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1869)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f119,f146,f162,f171,f173,f211,f221,f276])).

fof(f276,plain,
    ( spl10_2
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl10_2
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f166,f177,f226,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f226,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_11 ),
    inference(resolution,[],[f220,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f220,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl10_11
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f177,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f176,f97])).

fof(f97,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f83,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f81,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f41,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f176,plain,
    ( ~ l1_struct_0(sK3)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f175,f127])).

fof(f127,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f89,f50])).

fof(f89,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f51])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f175,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_4 ),
    inference(resolution,[],[f118,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f118,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl10_4
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f166,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl10_2 ),
    inference(subsumption_resolution,[],[f165,f97])).

fof(f165,plain,
    ( ~ l1_struct_0(sK3)
    | ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl10_2 ),
    inference(subsumption_resolution,[],[f164,f131])).

fof(f131,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f93,f50])).

fof(f93,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f91,f45])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f44,f51])).

fof(f44,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f164,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl10_2 ),
    inference(resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_2
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f221,plain,
    ( spl10_11
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f84,f141,f218])).

fof(f141,plain,
    ( spl10_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f42,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f211,plain,(
    spl10_7 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl10_7 ),
    inference(subsumption_resolution,[],[f161,f131])).

fof(f161,plain,
    ( ~ l1_struct_0(sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl10_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f173,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl10_8 ),
    inference(subsumption_resolution,[],[f170,f127])).

fof(f170,plain,
    ( ~ l1_struct_0(sK2)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_8
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f171,plain,
    ( spl10_4
    | ~ spl10_8
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f122,f112,f168,f116])).

fof(f112,plain,
    ( spl10_3
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f122,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK2,sK3)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f120,f97])).

fof(f120,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK2,sK3)
    | ~ spl10_3 ),
    inference(resolution,[],[f114,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f114,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f162,plain,
    ( ~ spl10_2
    | ~ spl10_7
    | spl10_1 ),
    inference(avatar_split_clause,[],[f109,f99,f159,f103])).

fof(f99,plain,
    ( spl10_1
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f109,plain,
    ( ~ l1_struct_0(sK1)
    | ~ r1_tsep_1(sK1,sK3)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f107,f97])).

fof(f107,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | spl10_1 ),
    inference(resolution,[],[f101,f57])).

fof(f101,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f146,plain,(
    spl10_6 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl10_6 ),
    inference(subsumption_resolution,[],[f143,f89])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f119,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f40,f116,f112])).

fof(f40,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f39,f103,f99])).

fof(f39,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
