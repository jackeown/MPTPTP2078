%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:41 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 204 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  337 ( 598 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f48,f58,f60,f66,f92,f103,f116,f127,f140,f143,f173,f181,f189,f199])).

fof(f199,plain,
    ( ~ spl5_1
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(subsumption_resolution,[],[f197,f138])).

fof(f138,plain,
    ( m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_13
  <=> m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f196,f155])).

fof(f155,plain,
    ( ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_14
  <=> r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f196,plain,
    ( r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_12 ),
    inference(resolution,[],[f135,f43])).

fof(f43,plain,
    ( ! [X5] :
        ( ~ v3_pre_topc(X5,sK0)
        | r2_hidden(X5,u1_pre_topc(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f37,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f135,plain,
    ( v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_12
  <=> v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f189,plain,
    ( ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f53,f184])).

fof(f184,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f14,f159])).

fof(f159,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f156,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f156,plain,
    ( r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f14,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f53,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_3
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f181,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_15 ),
    inference(subsumption_resolution,[],[f179,f52])).

fof(f52,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f179,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_15 ),
    inference(subsumption_resolution,[],[f178,f37])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_2(sK1,sK0)
    | ~ spl5_2
    | spl5_15 ),
    inference(subsumption_resolution,[],[f176,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v1_tops_2(sK1,sK0)
    | spl5_15 ),
    inference(resolution,[],[f172,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f172,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_15
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f173,plain,
    ( ~ spl5_15
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f166,f89,f55,f51,f45,f35,f170])).

fof(f55,plain,
    ( spl5_4
  <=> r1_tarski(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( spl5_8
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f165,f47])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f164,f52])).

fof(f164,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f57,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f163,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(resolution,[],[f152,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0))
        | v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,
    ( ! [X4] :
        ( v3_pre_topc(X4,sK0)
        | ~ r2_hidden(X4,u1_pre_topc(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(sK2(sK0,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X3,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,sK1),X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f91,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f143,plain,
    ( ~ spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f141,f126])).

fof(f126,plain,
    ( r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_11
  <=> r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f141,plain,
    ( ~ r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0))
    | spl5_13 ),
    inference(resolution,[],[f139,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f139,plain,
    ( ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( spl5_12
    | ~ spl5_13
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f111,f100,f51,f45,f35,f137,f133])).

fof(f100,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f111,plain,
    ( ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f108,f102])).

fof(f102,plain,
    ( r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f108,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X2,sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f106,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1)
        | v3_pre_topc(X2,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f39,f53])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0)
        | v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f127,plain,
    ( spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f120,f113,f124])).

fof(f113,plain,
    ( spl5_10
  <=> r2_hidden(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f120,plain,
    ( r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f115,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f115,plain,
    ( r2_hidden(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( spl5_10
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f109,f100,f63,f113])).

fof(f63,plain,
    ( spl5_5
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f109,plain,
    ( r2_hidden(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK3(sK1,u1_pre_topc(sK0)),X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f102,f23])).

fof(f103,plain,
    ( spl5_9
    | spl5_4 ),
    inference(avatar_split_clause,[],[f98,f55,f100])).

fof(f98,plain,
    ( r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1)
    | spl5_4 ),
    inference(resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f92,plain,
    ( spl5_8
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f86,f51,f45,f35,f89])).

fof(f86,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f85,f47])).

fof(f85,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f40,f52])).

fof(f40,plain,
    ( ! [X2] :
        ( v1_tops_2(X2,sK0)
        | r2_hidden(sK2(sK0,X2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK2(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f45,f63])).

fof(f49,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f59,f55,f51])).

fof(f59,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f14,f57])).

fof(f58,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f13,f55,f51])).

fof(f13,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f15,f45])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:57:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (24187)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.55  % (24191)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.56  % (24191)Refutation not found, incomplete strategy% (24191)------------------------------
% 1.45/0.56  % (24191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (24191)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (24191)Memory used [KB]: 6140
% 1.45/0.56  % (24191)Time elapsed: 0.129 s
% 1.45/0.56  % (24191)------------------------------
% 1.45/0.56  % (24191)------------------------------
% 1.45/0.56  % (24190)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.45/0.56  % (24207)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.57  % (24199)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.57  % (24194)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.57  % (24192)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.57  % (24215)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.58  % (24209)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.58  % (24198)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.58  % (24201)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.63/0.58  % (24208)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.63/0.58  % (24207)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f200,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f38,f48,f58,f60,f66,f92,f103,f116,f127,f140,f143,f173,f181,f189,f199])).
% 1.63/0.58  fof(f199,plain,(
% 1.63/0.58    ~spl5_1 | ~spl5_12 | ~spl5_13 | spl5_14),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f198])).
% 1.63/0.58  fof(f198,plain,(
% 1.63/0.58    $false | (~spl5_1 | ~spl5_12 | ~spl5_13 | spl5_14)),
% 1.63/0.58    inference(subsumption_resolution,[],[f197,f138])).
% 1.63/0.58  fof(f138,plain,(
% 1.63/0.58    m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_13),
% 1.63/0.58    inference(avatar_component_clause,[],[f137])).
% 1.63/0.58  fof(f137,plain,(
% 1.63/0.58    spl5_13 <=> m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.63/0.58  fof(f197,plain,(
% 1.63/0.58    ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_12 | spl5_14)),
% 1.63/0.58    inference(subsumption_resolution,[],[f196,f155])).
% 1.63/0.58  fof(f155,plain,(
% 1.63/0.58    ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | spl5_14),
% 1.63/0.58    inference(avatar_component_clause,[],[f154])).
% 1.63/0.58  fof(f154,plain,(
% 1.63/0.58    spl5_14 <=> r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.63/0.58  fof(f196,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_12)),
% 1.63/0.58    inference(resolution,[],[f135,f43])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    ( ! [X5] : (~v3_pre_topc(X5,sK0) | r2_hidden(X5,u1_pre_topc(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_1),
% 1.63/0.58    inference(resolution,[],[f37,f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f4])).
% 1.63/0.58  fof(f4,axiom,(
% 1.63/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    l1_pre_topc(sK0) | ~spl5_1),
% 1.63/0.58    inference(avatar_component_clause,[],[f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    spl5_1 <=> l1_pre_topc(sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.63/0.58  fof(f135,plain,(
% 1.63/0.58    v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) | ~spl5_12),
% 1.63/0.58    inference(avatar_component_clause,[],[f133])).
% 1.63/0.58  fof(f133,plain,(
% 1.63/0.58    spl5_12 <=> v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.63/0.58  fof(f189,plain,(
% 1.63/0.58    ~spl5_3 | ~spl5_14),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f188])).
% 1.63/0.58  fof(f188,plain,(
% 1.63/0.58    $false | (~spl5_3 | ~spl5_14)),
% 1.63/0.58    inference(subsumption_resolution,[],[f53,f184])).
% 1.63/0.58  fof(f184,plain,(
% 1.63/0.58    ~v1_tops_2(sK1,sK0) | ~spl5_14),
% 1.63/0.58    inference(subsumption_resolution,[],[f14,f159])).
% 1.63/0.58  fof(f159,plain,(
% 1.63/0.58    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl5_14),
% 1.63/0.58    inference(resolution,[],[f156,f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f12])).
% 1.63/0.58  fof(f12,plain,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.58  fof(f156,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~spl5_14),
% 1.63/0.58    inference(avatar_component_clause,[],[f154])).
% 1.63/0.58  fof(f14,plain,(
% 1.63/0.58    ~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,plain,(
% 1.63/0.58    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,negated_conjecture,(
% 1.63/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 1.63/0.58    inference(negated_conjecture,[],[f6])).
% 1.63/0.58  fof(f6,conjecture,(
% 1.63/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 1.63/0.58  fof(f53,plain,(
% 1.63/0.58    v1_tops_2(sK1,sK0) | ~spl5_3),
% 1.63/0.58    inference(avatar_component_clause,[],[f51])).
% 1.63/0.58  fof(f51,plain,(
% 1.63/0.58    spl5_3 <=> v1_tops_2(sK1,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.63/0.58  fof(f181,plain,(
% 1.63/0.58    ~spl5_1 | ~spl5_2 | spl5_3 | spl5_15),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f180])).
% 1.63/0.58  fof(f180,plain,(
% 1.63/0.58    $false | (~spl5_1 | ~spl5_2 | spl5_3 | spl5_15)),
% 1.63/0.58    inference(subsumption_resolution,[],[f179,f52])).
% 1.63/0.58  fof(f52,plain,(
% 1.63/0.58    ~v1_tops_2(sK1,sK0) | spl5_3),
% 1.63/0.58    inference(avatar_component_clause,[],[f51])).
% 1.63/0.58  fof(f179,plain,(
% 1.63/0.58    v1_tops_2(sK1,sK0) | (~spl5_1 | ~spl5_2 | spl5_15)),
% 1.63/0.58    inference(subsumption_resolution,[],[f178,f37])).
% 1.63/0.58  fof(f178,plain,(
% 1.63/0.58    ~l1_pre_topc(sK0) | v1_tops_2(sK1,sK0) | (~spl5_2 | spl5_15)),
% 1.63/0.58    inference(subsumption_resolution,[],[f176,f47])).
% 1.63/0.58  fof(f47,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f45])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.63/0.58  fof(f176,plain,(
% 1.63/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v1_tops_2(sK1,sK0) | spl5_15),
% 1.63/0.58    inference(resolution,[],[f172,f20])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v1_tops_2(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f11])).
% 1.63/0.58  fof(f11,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(flattening,[],[f10])).
% 1.63/0.58  fof(f10,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 1.63/0.58  fof(f172,plain,(
% 1.63/0.58    ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_15),
% 1.63/0.58    inference(avatar_component_clause,[],[f170])).
% 1.63/0.58  fof(f170,plain,(
% 1.63/0.58    spl5_15 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.63/0.58  fof(f173,plain,(
% 1.63/0.58    ~spl5_15 | ~spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f166,f89,f55,f51,f45,f35,f170])).
% 1.63/0.58  fof(f55,plain,(
% 1.63/0.58    spl5_4 <=> r1_tarski(sK1,u1_pre_topc(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.63/0.58  fof(f89,plain,(
% 1.63/0.58    spl5_8 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.63/0.58  fof(f166,plain,(
% 1.63/0.58    ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_8)),
% 1.63/0.58    inference(subsumption_resolution,[],[f165,f47])).
% 1.63/0.58  fof(f165,plain,(
% 1.63/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_8)),
% 1.63/0.58    inference(subsumption_resolution,[],[f164,f52])).
% 1.63/0.58  fof(f164,plain,(
% 1.63/0.58    v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_4 | ~spl5_8)),
% 1.63/0.58    inference(subsumption_resolution,[],[f163,f57])).
% 1.63/0.58  fof(f57,plain,(
% 1.63/0.58    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl5_4),
% 1.63/0.58    inference(avatar_component_clause,[],[f55])).
% 1.63/0.58  fof(f163,plain,(
% 1.63/0.58    ~r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_8)),
% 1.63/0.58    inference(resolution,[],[f152,f87])).
% 1.63/0.58  fof(f87,plain,(
% 1.63/0.58    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0)) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_1),
% 1.63/0.58    inference(resolution,[],[f41,f42])).
% 1.63/0.58  fof(f42,plain,(
% 1.63/0.58    ( ! [X4] : (v3_pre_topc(X4,sK0) | ~r2_hidden(X4,u1_pre_topc(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_1),
% 1.63/0.58    inference(resolution,[],[f37,f17])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f9])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ( ! [X3] : (~v3_pre_topc(sK2(sK0,X3),sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X3,sK0)) ) | ~spl5_1),
% 1.63/0.58    inference(resolution,[],[f37,f22])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(sK2(X0,X1),X0) | v1_tops_2(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f11])).
% 1.63/0.58  fof(f152,plain,(
% 1.63/0.58    ( ! [X0] : (r2_hidden(sK2(sK0,sK1),X0) | ~r1_tarski(sK1,X0)) ) | ~spl5_8),
% 1.63/0.58    inference(resolution,[],[f91,f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f12])).
% 1.63/0.58  fof(f91,plain,(
% 1.63/0.58    r2_hidden(sK2(sK0,sK1),sK1) | ~spl5_8),
% 1.63/0.58    inference(avatar_component_clause,[],[f89])).
% 1.63/0.58  fof(f143,plain,(
% 1.63/0.58    ~spl5_11 | spl5_13),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f142])).
% 1.63/0.58  fof(f142,plain,(
% 1.63/0.58    $false | (~spl5_11 | spl5_13)),
% 1.63/0.58    inference(subsumption_resolution,[],[f141,f126])).
% 1.63/0.58  fof(f126,plain,(
% 1.63/0.58    r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0)) | ~spl5_11),
% 1.63/0.58    inference(avatar_component_clause,[],[f124])).
% 1.63/0.58  fof(f124,plain,(
% 1.63/0.58    spl5_11 <=> r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.63/0.58  fof(f141,plain,(
% 1.63/0.58    ~r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0)) | spl5_13),
% 1.63/0.58    inference(resolution,[],[f139,f30])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.58  fof(f139,plain,(
% 1.63/0.58    ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_13),
% 1.63/0.58    inference(avatar_component_clause,[],[f137])).
% 1.63/0.58  fof(f140,plain,(
% 1.63/0.58    spl5_12 | ~spl5_13 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f111,f100,f51,f45,f35,f137,f133])).
% 1.63/0.58  fof(f100,plain,(
% 1.63/0.58    spl5_9 <=> r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.63/0.58  fof(f111,plain,(
% 1.63/0.58    ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_9)),
% 1.63/0.58    inference(resolution,[],[f108,f102])).
% 1.63/0.58  fof(f102,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1) | ~spl5_9),
% 1.63/0.58    inference(avatar_component_clause,[],[f100])).
% 1.63/0.58  fof(f108,plain,(
% 1.63/0.58    ( ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X2,sK0)) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.63/0.58    inference(subsumption_resolution,[],[f106,f47])).
% 1.63/0.58  fof(f106,plain,(
% 1.63/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1) | v3_pre_topc(X2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl5_1 | ~spl5_3)),
% 1.63/0.58    inference(resolution,[],[f39,f53])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~v1_tops_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0) | v3_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl5_1),
% 1.63/0.58    inference(resolution,[],[f37,f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f11])).
% 1.63/0.58  fof(f127,plain,(
% 1.63/0.58    spl5_11 | ~spl5_10),
% 1.63/0.58    inference(avatar_split_clause,[],[f120,f113,f124])).
% 1.63/0.58  fof(f113,plain,(
% 1.63/0.58    spl5_10 <=> r2_hidden(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.63/0.58  fof(f120,plain,(
% 1.63/0.58    r1_tarski(sK3(sK1,u1_pre_topc(sK0)),u1_struct_0(sK0)) | ~spl5_10),
% 1.63/0.58    inference(resolution,[],[f115,f32])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.63/0.58    inference(equality_resolution,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.63/0.58    inference(cnf_transformation,[],[f2])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.63/0.58  fof(f115,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_10),
% 1.63/0.58    inference(avatar_component_clause,[],[f113])).
% 1.63/0.58  fof(f116,plain,(
% 1.63/0.58    spl5_10 | ~spl5_5 | ~spl5_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f109,f100,f63,f113])).
% 1.63/0.58  fof(f63,plain,(
% 1.63/0.58    spl5_5 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.63/0.58  fof(f109,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_5 | ~spl5_9)),
% 1.63/0.58    inference(resolution,[],[f104,f65])).
% 1.63/0.58  fof(f65,plain,(
% 1.63/0.58    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 1.63/0.58    inference(avatar_component_clause,[],[f63])).
% 1.63/0.58  fof(f104,plain,(
% 1.63/0.58    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK3(sK1,u1_pre_topc(sK0)),X0)) ) | ~spl5_9),
% 1.63/0.58    inference(resolution,[],[f102,f23])).
% 1.63/0.58  fof(f103,plain,(
% 1.63/0.58    spl5_9 | spl5_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f98,f55,f100])).
% 1.63/0.58  fof(f98,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1) | spl5_4),
% 1.63/0.58    inference(resolution,[],[f56,f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f12])).
% 1.63/0.58  fof(f56,plain,(
% 1.63/0.58    ~r1_tarski(sK1,u1_pre_topc(sK0)) | spl5_4),
% 1.63/0.58    inference(avatar_component_clause,[],[f55])).
% 1.63/0.58  fof(f92,plain,(
% 1.63/0.58    spl5_8 | ~spl5_1 | ~spl5_2 | spl5_3),
% 1.63/0.58    inference(avatar_split_clause,[],[f86,f51,f45,f35,f89])).
% 1.63/0.58  fof(f86,plain,(
% 1.63/0.58    r2_hidden(sK2(sK0,sK1),sK1) | (~spl5_1 | ~spl5_2 | spl5_3)),
% 1.63/0.58    inference(subsumption_resolution,[],[f85,f47])).
% 1.63/0.58  fof(f85,plain,(
% 1.63/0.58    r2_hidden(sK2(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_1 | spl5_3)),
% 1.63/0.58    inference(resolution,[],[f40,f52])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ( ! [X2] : (v1_tops_2(X2,sK0) | r2_hidden(sK2(sK0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl5_1),
% 1.63/0.58    inference(resolution,[],[f37,f21])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2(X0,X1),X1) | v1_tops_2(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f11])).
% 1.63/0.58  fof(f66,plain,(
% 1.63/0.58    spl5_5 | ~spl5_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f49,f45,f63])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 1.63/0.58    inference(resolution,[],[f47,f31])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f3])).
% 1.63/0.58  fof(f60,plain,(
% 1.63/0.58    ~spl5_3 | ~spl5_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f59,f55,f51])).
% 1.63/0.58  fof(f59,plain,(
% 1.63/0.58    ~v1_tops_2(sK1,sK0) | ~spl5_4),
% 1.63/0.58    inference(subsumption_resolution,[],[f14,f57])).
% 1.63/0.58  fof(f58,plain,(
% 1.63/0.58    spl5_3 | spl5_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f13,f55,f51])).
% 1.63/0.58  fof(f13,plain,(
% 1.63/0.58    r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f8])).
% 1.63/0.58  fof(f48,plain,(
% 1.63/0.58    spl5_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f15,f45])).
% 1.63/0.58  fof(f15,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.58    inference(cnf_transformation,[],[f8])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    spl5_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f16,f35])).
% 1.63/0.58  fof(f16,plain,(
% 1.63/0.58    l1_pre_topc(sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f8])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (24207)------------------------------
% 1.63/0.58  % (24207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (24207)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (24207)Memory used [KB]: 10874
% 1.63/0.58  % (24207)Time elapsed: 0.151 s
% 1.63/0.58  % (24207)------------------------------
% 1.63/0.58  % (24207)------------------------------
% 1.63/0.58  % (24197)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.63/0.58  % (24186)Success in time 0.215 s
%------------------------------------------------------------------------------
