%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 202 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  315 ( 726 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31276)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f83,f108,f135,f161,f170,f261,f374,f479,f533])).

fof(f533,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f479,plain,
    ( spl3_64
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f474,f132,f105,f80,f63,f476])).

fof(f476,plain,
    ( spl3_64
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f63,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f105,plain,
    ( spl3_11
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f132,plain,
    ( spl3_15
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f474,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f473,f116])).

% (31285)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f116,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f473,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f409,f107])).

fof(f107,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f409,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f82,f134,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f134,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f82,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f374,plain,
    ( spl3_50
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f369,f258,f166,f80,f73,f68,f58,f371])).

fof(f371,plain,
    ( spl3_50
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f58,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f73,plain,
    ( spl3_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f166,plain,
    ( spl3_20
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f258,plain,
    ( spl3_33
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f369,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f368,f168])).

fof(f168,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f368,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f292,f260])).

fof(f260,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f292,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f75,f70,f60,f82,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f261,plain,
    ( spl3_33
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f256,f105,f80,f63,f58,f258])).

fof(f256,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f255,f116])).

fof(f255,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,sK1) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f175,f107])).

fof(f175,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f60,f82,f39])).

fof(f170,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_20
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f164,f158,f166,f80,f68])).

fof(f158,plain,
    ( spl3_19
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f164,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_19 ),
    inference(resolution,[],[f160,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f160,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f155,f68,f63,f53,f158])).

fof(f53,plain,
    ( spl3_2
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f155,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f70,f55,f65,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f55,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f135,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f118,f68,f58,f132])).

fof(f118,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f70,f60,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f108,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f96,f63,f105])).

fof(f96,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f78,f63,f80])).

fof(f78,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f76,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)))
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)))
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)))
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)))
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X1,X0)
                 => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tops_1)).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f53])).

fof(f35,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f48])).

fof(f48,plain,
    ( spl3_1
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (31279)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (31287)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (31270)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (31286)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.49  % (31274)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (31273)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (31291)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (31278)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (31283)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (31290)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (31289)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (31271)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (31275)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (31272)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (31272)Refutation not found, incomplete strategy% (31272)------------------------------
% 0.20/0.51  % (31272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31272)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31272)Memory used [KB]: 10618
% 0.20/0.51  % (31272)Time elapsed: 0.094 s
% 0.20/0.51  % (31272)------------------------------
% 0.20/0.51  % (31272)------------------------------
% 0.20/0.51  % (31282)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (31269)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (31281)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.52  % (31292)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  % (31280)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (31292)Refutation not found, incomplete strategy% (31292)------------------------------
% 0.20/0.52  % (31292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31292)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31292)Memory used [KB]: 10618
% 0.20/0.52  % (31292)Time elapsed: 0.111 s
% 0.20/0.52  % (31292)------------------------------
% 0.20/0.52  % (31292)------------------------------
% 0.20/0.52  % (31275)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  % (31276)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  fof(f534,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f83,f108,f135,f161,f170,f261,f374,f479,f533])).
% 0.20/0.52  fof(f533,plain,(
% 0.20/0.52    k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f479,plain,(
% 0.20/0.52    spl3_64 | ~spl3_4 | ~spl3_7 | ~spl3_11 | ~spl3_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f474,f132,f105,f80,f63,f476])).
% 0.20/0.52  fof(f476,plain,(
% 0.20/0.52    spl3_64 <=> k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    spl3_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl3_11 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl3_15 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.52  fof(f474,plain,(
% 0.20/0.52    k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_4 | ~spl3_7 | ~spl3_11 | ~spl3_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f473,f116])).
% 0.20/0.52  % (31285)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_4),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f65,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f473,plain,(
% 0.20/0.52    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_7 | ~spl3_11 | ~spl3_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f409,f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f105])).
% 0.20/0.52  fof(f409,plain,(
% 0.20/0.52    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_7 | ~spl3_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f82,f134,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f132])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f80])).
% 0.20/0.52  fof(f374,plain,(
% 0.20/0.52    spl3_50 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_20 | ~spl3_33),
% 0.20/0.52    inference(avatar_split_clause,[],[f369,f258,f166,f80,f73,f68,f58,f371])).
% 0.20/0.52  fof(f371,plain,(
% 0.20/0.52    spl3_50 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl3_5 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl3_6 <=> v2_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    spl3_20 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.52  fof(f258,plain,(
% 0.20/0.52    spl3_33 <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.52  fof(f369,plain,(
% 0.20/0.52    r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_20 | ~spl3_33)),
% 0.20/0.52    inference(forward_demodulation,[],[f368,f168])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f166])).
% 0.20/0.52  fof(f368,plain,(
% 0.20/0.52    r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_33)),
% 0.20/0.52    inference(forward_demodulation,[],[f292,f260])).
% 0.20/0.52  fof(f260,plain,(
% 0.20/0.52    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_33),
% 0.20/0.52    inference(avatar_component_clause,[],[f258])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f70,f60,f82,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f58])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    l1_pre_topc(sK0) | ~spl3_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    v2_pre_topc(sK0) | ~spl3_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    spl3_33 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f256,f105,f80,f63,f58,f258])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_11)),
% 0.20/0.52    inference(forward_demodulation,[],[f255,f116])).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    k9_subset_1(u1_struct_0(sK0),sK2,sK1) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.20/0.52    inference(forward_demodulation,[],[f175,f107])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_3 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f60,f82,f39])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ~spl3_5 | ~spl3_7 | spl3_20 | ~spl3_19),
% 0.20/0.52    inference(avatar_split_clause,[],[f164,f158,f166,f80,f68])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl3_19 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_19),
% 0.20/0.52    inference(resolution,[],[f160,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f158])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    spl3_19 | ~spl3_2 | ~spl3_4 | ~spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f155,f68,f63,f53,f158])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    spl3_2 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f70,f55,f65,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0) | ~spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f53])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl3_15 | ~spl3_3 | ~spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f118,f68,f58,f132])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_5)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f70,f60,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl3_11 | ~spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f96,f63,f105])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_4),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f65,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl3_7 | ~spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f78,f63,f80])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f65,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl3_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f31,f73])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ((~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28,f27,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2))) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2))) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2))) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2))) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tops_1)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f32,f68])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f33,f63])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f34,f58])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f53])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ~spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    spl3_1 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (31275)------------------------------
% 0.20/0.52  % (31275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31275)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (31275)Memory used [KB]: 11129
% 0.20/0.52  % (31275)Time elapsed: 0.074 s
% 0.20/0.52  % (31275)------------------------------
% 0.20/0.52  % (31275)------------------------------
% 0.20/0.52  % (31268)Success in time 0.165 s
%------------------------------------------------------------------------------
