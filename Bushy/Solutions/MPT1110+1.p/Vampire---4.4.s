%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t39_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:43 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 131 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  194 ( 325 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f111,f115,f128,f132,f139,f143,f166,f182,f190,f381,f398])).

fof(f398,plain,
    ( spl10_11
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl10_11
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f395,f138])).

fof(f138,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_11
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_64 ),
    inference(resolution,[],[f380,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',t3_subset)).

fof(f380,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl10_64
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f381,plain,
    ( spl10_64
    | ~ spl10_16
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f377,f188,f164,f379])).

fof(f164,plain,
    ( spl10_16
  <=> r1_tarski(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f188,plain,
    ( spl10_22
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f377,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl10_16
    | ~ spl10_22 ),
    inference(resolution,[],[f174,f189])).

fof(f189,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f188])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl10_16 ),
    inference(resolution,[],[f165,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',t1_xboole_1)).

fof(f165,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f190,plain,
    ( spl10_22
    | ~ spl10_12
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f183,f180,f141,f188])).

fof(f141,plain,
    ( spl10_12
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f180,plain,
    ( spl10_20
  <=> r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f183,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_12
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f181,f156])).

fof(f156,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl10_12 ),
    inference(resolution,[],[f142,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',d3_struct_0)).

fof(f142,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f181,plain,
    ( r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl10_20
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f124,f113,f109,f102,f180])).

fof(f102,plain,
    ( spl10_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f109,plain,
    ( spl10_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f113,plain,
    ( spl10_4
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f124,plain,
    ( r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f122,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f120,f103])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f102])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl10_4 ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',dt_m1_pre_topc)).

fof(f114,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f122,plain,
    ( r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f121,f116])).

fof(f116,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f110,f68])).

fof(f110,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f119,f103])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(resolution,[],[f114,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',d9_pre_topc)).

fof(f166,plain,
    ( spl10_16
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f147,f130,f164])).

fof(f130,plain,
    ( spl10_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f147,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1))
    | ~ spl10_8 ),
    inference(resolution,[],[f131,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f143,plain,
    ( spl10_12
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f134,f126,f141])).

fof(f126,plain,
    ( spl10_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f134,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f127,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',dt_l1_pre_topc)).

fof(f127,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f139,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f61,f137])).

fof(f61,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t39_pre_topc.p',t39_pre_topc)).

fof(f132,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f60,f130])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,
    ( spl10_6
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f123,f113,f102,f126])).

fof(f115,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f62,f113])).

fof(f62,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,
    ( spl10_2
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f106,f102,f109])).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_0 ),
    inference(resolution,[],[f103,f82])).

fof(f104,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f63,f102])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
