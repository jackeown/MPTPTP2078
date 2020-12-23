%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t20_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:50 EDT 2019

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  563 (2828 expanded)
%              Number of leaves         :  139 (1064 expanded)
%              Depth                    :   14
%              Number of atoms          : 1938 (7953 expanded)
%              Number of equality atoms :   63 ( 489 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26578,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f116,f123,f130,f137,f144,f151,f158,f165,f172,f182,f208,f215,f258,f271,f291,f301,f312,f326,f330,f399,f432,f1737,f1748,f3066,f3080,f3088,f3152,f3172,f3304,f3318,f3326,f3374,f3384,f3481,f3494,f5597,f5612,f6549,f6563,f6577,f6591,f6601,f6675,f8359,f8374,f8388,f8547,f8575,f8584,f8593,f8600,f8607,f8617,f8626,f8875,f12060,f12078,f12381,f12404,f12586,f12606,f12608,f12614,f12639,f12658,f12705,f12724,f12740,f12744,f12757,f12770,f16725,f16732,f16739,f16753,f16760,f16768,f16775,f16782,f16790,f16794,f16798,f16807,f16818,f17447,f19059,f19078,f19097,f19116,f21595,f21598,f22302,f25142,f25148,f25468,f25485,f25502,f25519,f26574,f26577])).

fof(f26577,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_18
    | spl5_49
    | ~ spl5_120 ),
    inference(avatar_contradiction_clause,[],[f26576])).

fof(f26576,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f26575,f171])).

fof(f171,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f26575,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f26571,f186])).

fof(f186,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f85,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',commutativity_k3_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t17_xboole_1)).

fof(f26571,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(resolution,[],[f12066,f150])).

fof(f150,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_12
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f12066,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f12065,f431])).

fof(f431,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl5_49
  <=> ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f12065,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(k3_xboole_0(sK1,sK2),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f12062,f389])).

fof(f389,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(superposition,[],[f369,f86])).

fof(f369,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(superposition,[],[f335,f359])).

fof(f359,plain,
    ( ! [X8] : k9_subset_1(u1_struct_0(sK0),X8,sK1) = k3_xboole_0(X8,sK1)
    | ~ spl5_16 ),
    inference(resolution,[],[f96,f164])).

fof(f164,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',redefinition_k9_subset_1)).

fof(f335,plain,
    ( ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X4,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(resolution,[],[f95,f164])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',dt_k9_subset_1)).

fof(f12062,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(k3_xboole_0(sK1,sK2),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(resolution,[],[f12059,f1793])).

fof(f1793,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,sK0) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1792,f115])).

fof(f115,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1792,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_compts_1(X0,sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f82,f108])).

fof(f108,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t18_compts_1)).

fof(f12059,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f12058])).

fof(f12058,plain,
    ( spl5_120
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f26574,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | spl5_49
    | ~ spl5_120 ),
    inference(avatar_contradiction_clause,[],[f26573])).

fof(f26573,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f26572,f164])).

fof(f26572,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f26570,f85])).

fof(f26570,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_120 ),
    inference(resolution,[],[f12066,f143])).

fof(f143,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_10
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f25519,plain,
    ( spl5_212
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f12729,f12722,f1746,f170,f163,f114,f107,f25517])).

fof(f25517,plain,
    ( spl5_212
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).

fof(f1746,plain,
    ( spl5_52
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f12722,plain,
    ( spl5_142
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f12729,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f12725,f389])).

fof(f12725,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_142 ),
    inference(resolution,[],[f12723,f1752])).

fof(f1752,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_xboole_0(sK2,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1751,f108])).

fof(f1751,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1750,f115])).

fof(f1750,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_18
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1749,f171])).

fof(f1749,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_52 ),
    inference(resolution,[],[f1747,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',fc4_tops_1)).

fof(f1747,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f1746])).

fof(f12723,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f12722])).

fof(f25502,plain,
    ( spl5_210
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_140 ),
    inference(avatar_split_clause,[],[f12711,f12703,f1735,f170,f163,f114,f107,f25500])).

fof(f25500,plain,
    ( spl5_210
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f1735,plain,
    ( spl5_50
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f12703,plain,
    ( spl5_140
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f12711,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_140 ),
    inference(subsumption_resolution,[],[f12707,f450])).

fof(f450,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(superposition,[],[f423,f86])).

fof(f423,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(superposition,[],[f336,f360])).

fof(f360,plain,
    ( ! [X9] : k9_subset_1(u1_struct_0(sK0),X9,sK2) = k3_xboole_0(X9,sK2)
    | ~ spl5_18 ),
    inference(resolution,[],[f96,f171])).

fof(f336,plain,
    ( ! [X5] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X5,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(resolution,[],[f95,f171])).

fof(f12707,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_140 ),
    inference(resolution,[],[f12704,f1741])).

fof(f1741,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_xboole_0(sK1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1740,f108])).

fof(f1740,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1739,f115])).

fof(f1739,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_16
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1738,f164])).

fof(f1738,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_50 ),
    inference(resolution,[],[f1736,f98])).

fof(f1736,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f12704,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_140 ),
    inference(avatar_component_clause,[],[f12703])).

fof(f25485,plain,
    ( spl5_208
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f12664,f12656,f1735,f170,f163,f114,f107,f25483])).

fof(f25483,plain,
    ( spl5_208
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f12656,plain,
    ( spl5_138
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f12664,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_138 ),
    inference(subsumption_resolution,[],[f12660,f450])).

fof(f12660,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_138 ),
    inference(resolution,[],[f12657,f1741])).

fof(f12657,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_138 ),
    inference(avatar_component_clause,[],[f12656])).

fof(f25468,plain,
    ( spl5_206
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f12626,f12379,f1746,f170,f163,f114,f107,f25466])).

fof(f25466,plain,
    ( spl5_206
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f12379,plain,
    ( spl5_124
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f12626,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_124 ),
    inference(subsumption_resolution,[],[f12619,f389])).

fof(f12619,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_124 ),
    inference(resolution,[],[f1752,f12380])).

fof(f12380,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f12379])).

fof(f25148,plain,
    ( spl5_68
    | spl5_204
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f16629,f3302,f25146,f3473])).

fof(f3473,plain,
    ( spl5_68
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f25146,plain,
    ( spl5_204
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),sK3(X1))
        | v1_xboole_0(sK3(X1))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f3302,plain,
    ( spl5_60
  <=> ! [X184] :
        ( m1_subset_1(X184,u1_struct_0(sK0))
        | ~ m1_subset_1(X184,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f16629,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | v1_xboole_0(X1)
        | v1_xboole_0(sK3(X1))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),sK3(X1)) )
    | ~ spl5_60 ),
    inference(resolution,[],[f16616,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f219,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t2_subset)).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',antisymmetry_r2_hidden)).

fof(f16616,plain,
    ( ! [X74] :
        ( m1_subset_1(sK3(X74),u1_struct_0(sK0))
        | ~ r1_tarski(X74,sK2)
        | v1_xboole_0(X74) )
    | ~ spl5_60 ),
    inference(resolution,[],[f16528,f3303])).

fof(f3303,plain,
    ( ! [X184] :
        ( ~ m1_subset_1(X184,sK2)
        | m1_subset_1(X184,u1_struct_0(sK0)) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f3302])).

fof(f16528,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK3(X5),X4)
      | v1_xboole_0(X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(forward_demodulation,[],[f16490,f227])).

fof(f227,plain,(
    ! [X6,X5] : k9_subset_1(X5,X6,X6) = X6 ),
    inference(resolution,[],[f94,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',existence_m1_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',idempotence_k9_subset_1)).

fof(f16490,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK3(X5),X4)
      | v1_xboole_0(k9_subset_1(X4,X5,X5))
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f10237,f227])).

fof(f10237,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(k9_subset_1(X0,X1,X2)),X0)
      | v1_xboole_0(k9_subset_1(X0,X1,X2))
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f2998,f83])).

fof(f2998,plain,(
    ! [X23,X21,X22,X20] :
      ( ~ m1_subset_1(X20,k9_subset_1(X21,X22,X23))
      | v1_xboole_0(k9_subset_1(X21,X22,X23))
      | m1_subset_1(X20,X21)
      | ~ r1_tarski(X23,X21) ) ),
    inference(resolution,[],[f235,f333])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f95,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t3_subset)).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f99,f89])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t4_subset)).

fof(f25142,plain,
    ( spl5_68
    | spl5_202
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f16624,f3064,f25140,f3473])).

fof(f25140,plain,
    ( spl5_202
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),sK3(X1))
        | v1_xboole_0(sK3(X1))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f3064,plain,
    ( spl5_54
  <=> ! [X183] :
        ( m1_subset_1(X183,u1_struct_0(sK0))
        | ~ m1_subset_1(X183,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f16624,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | v1_xboole_0(X1)
        | v1_xboole_0(sK3(X1))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),sK3(X1)) )
    | ~ spl5_54 ),
    inference(resolution,[],[f16615,f221])).

fof(f16615,plain,
    ( ! [X73] :
        ( m1_subset_1(sK3(X73),u1_struct_0(sK0))
        | ~ r1_tarski(X73,sK1)
        | v1_xboole_0(X73) )
    | ~ spl5_54 ),
    inference(resolution,[],[f16528,f3065])).

fof(f3065,plain,
    ( ! [X183] :
        ( ~ m1_subset_1(X183,sK1)
        | m1_subset_1(X183,u1_struct_0(sK0)) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f3064])).

fof(f22302,plain,
    ( ~ spl5_199
    | spl5_200
    | ~ spl5_16
    | spl5_29 ),
    inference(avatar_split_clause,[],[f22289,f247,f163,f22300,f22294])).

fof(f22294,plain,
    ( spl5_199
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f22300,plain,
    ( spl5_200
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f247,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f22289,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(resolution,[],[f22237,f2530])).

fof(f2530,plain,(
    ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(superposition,[],[f2516,f84])).

fof(f84,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',idempotence_k3_xboole_0)).

fof(f2516,plain,(
    ! [X8,X7] : m1_subset_1(k3_xboole_0(X8,X7),k1_zfmisc_1(X7)) ),
    inference(subsumption_resolution,[],[f2505,f175])).

fof(f175,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f85,f84])).

fof(f2505,plain,(
    ! [X8,X7] :
      ( m1_subset_1(k3_xboole_0(X8,X7),k1_zfmisc_1(X7))
      | ~ r1_tarski(X7,X7) ) ),
    inference(superposition,[],[f333,f2421])).

fof(f2421,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(resolution,[],[f355,f175])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f96,f91])).

fof(f22237,plain,
    ( ! [X42] :
        ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X42)
        | v1_xboole_0(X42)
        | ~ r1_tarski(X42,u1_struct_0(sK0)) )
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f22236,f225])).

fof(f225,plain,
    ( ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,X3) = X3
    | ~ spl5_16 ),
    inference(resolution,[],[f94,f164])).

fof(f22236,plain,
    ( ! [X42] :
        ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X42)
        | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X42,X42))
        | ~ r1_tarski(X42,u1_struct_0(sK0)) )
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f22188,f248])).

fof(f248,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f247])).

fof(f22188,plain,
    ( ! [X42] :
        ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X42)
        | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X42,X42))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X42,u1_struct_0(sK0)) )
    | ~ spl5_16 ),
    inference(superposition,[],[f1438,f225])).

fof(f1438,plain,(
    ! [X24,X23,X25] :
      ( ~ m1_subset_1(k1_zfmisc_1(X24),k9_subset_1(X24,X25,X23))
      | v1_xboole_0(k9_subset_1(X24,X25,X23))
      | v1_xboole_0(k1_zfmisc_1(X24))
      | ~ r1_tarski(X23,X24) ) ),
    inference(resolution,[],[f333,f221])).

fof(f21598,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | spl5_49
    | ~ spl5_100
    | ~ spl5_106
    | ~ spl5_120 ),
    inference(avatar_contradiction_clause,[],[f21597])).

fof(f21597,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_106
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f21596,f8583])).

fof(f8583,plain,
    ( m1_subset_1(sK2,k1_xboole_0)
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f8582])).

fof(f8582,plain,
    ( spl5_106
  <=> m1_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f21596,plain,
    ( ~ m1_subset_1(sK2,k1_xboole_0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f21592,f186])).

fof(f21592,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_xboole_0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_120 ),
    inference(resolution,[],[f12067,f150])).

fof(f12067,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f12066,f8373])).

fof(f8373,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f8372])).

fof(f8372,plain,
    ( spl5_100
  <=> k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f21595,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | spl5_49
    | ~ spl5_100
    | ~ spl5_104
    | ~ spl5_120 ),
    inference(avatar_contradiction_clause,[],[f21594])).

fof(f21594,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_104
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f21593,f8574])).

fof(f8574,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f8573])).

fof(f8573,plain,
    ( spl5_104
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f21593,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f21591,f85])).

fof(f21591,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_49
    | ~ spl5_100
    | ~ spl5_120 ),
    inference(resolution,[],[f12067,f143])).

fof(f19116,plain,
    ( spl5_196
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f12730,f12722,f1735,f163,f114,f107,f19114])).

fof(f19114,plain,
    ( spl5_196
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f12730,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f12726,f389])).

fof(f12726,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_142 ),
    inference(resolution,[],[f12723,f1741])).

fof(f19097,plain,
    ( spl5_194
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_140 ),
    inference(avatar_split_clause,[],[f12710,f12703,f1746,f170,f114,f107,f19095])).

fof(f19095,plain,
    ( spl5_194
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f12710,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_140 ),
    inference(subsumption_resolution,[],[f12706,f450])).

fof(f12706,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_140 ),
    inference(resolution,[],[f12704,f1752])).

fof(f19078,plain,
    ( spl5_192
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f12663,f12656,f1746,f170,f114,f107,f19076])).

fof(f19076,plain,
    ( spl5_192
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f12663,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(subsumption_resolution,[],[f12659,f450])).

fof(f12659,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(resolution,[],[f12657,f1752])).

fof(f19059,plain,
    ( spl5_190
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f12385,f12379,f1735,f163,f114,f107,f19057])).

fof(f19057,plain,
    ( spl5_190
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f12385,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_124 ),
    inference(subsumption_resolution,[],[f12382,f389])).

fof(f12382,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_124 ),
    inference(resolution,[],[f12380,f1741])).

fof(f17447,plain,
    ( spl5_28
    | spl5_188
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f352,f170,f17445,f250])).

fof(f250,plain,
    ( spl5_28
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f17445,plain,
    ( spl5_188
  <=> ! [X4] :
        ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X4,sK2))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(u1_struct_0(sK0),X4,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f352,plain,
    ( ! [X4] :
        ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X4,sK2))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(u1_struct_0(sK0),X4,sK2)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f336,f221])).

fof(f16818,plain,
    ( ~ spl5_187
    | spl5_160
    | spl5_87
    | ~ spl5_88
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f16811,f8372,f6561,f6544,f16723,f16816])).

fof(f16816,plain,
    ( spl5_187
  <=> ~ m1_subset_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f16723,plain,
    ( spl5_160
  <=> m1_subset_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f6544,plain,
    ( spl5_87
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f6561,plain,
    ( spl5_88
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f16811,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl5_87
    | ~ spl5_88
    | ~ spl5_100 ),
    inference(resolution,[],[f16622,f8461])).

fof(f8461,plain,
    ( ! [X202] :
        ( r1_tarski(X202,u1_struct_0(sK0))
        | ~ m1_subset_1(X202,k1_xboole_0) )
    | ~ spl5_100 ),
    inference(superposition,[],[f90,f8373])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f16622,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),X1)
        | m1_subset_1(k1_xboole_0,X1) )
    | ~ spl5_87
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f16621,f6545])).

fof(f6545,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f6544])).

fof(f16621,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,X1)
        | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),X1) )
    | ~ spl5_88 ),
    inference(superposition,[],[f16528,f6562])).

fof(f6562,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f6561])).

fof(f16807,plain,
    ( ~ spl5_185
    | spl5_160
    | ~ spl5_100
    | ~ spl5_182 ),
    inference(avatar_split_clause,[],[f16800,f16796,f8372,f16723,f16805])).

fof(f16805,plain,
    ( spl5_185
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f16796,plain,
    ( spl5_182
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f16800,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_100
    | ~ spl5_182 ),
    inference(resolution,[],[f16797,f8461])).

fof(f16797,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0)
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl5_182 ),
    inference(avatar_component_clause,[],[f16796])).

fof(f16798,plain,
    ( spl5_156
    | spl5_182
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f16620,f299,f16796,f16711])).

fof(f16711,plain,
    ( spl5_156
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f299,plain,
    ( spl5_38
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f16620,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0) )
    | ~ spl5_38 ),
    inference(superposition,[],[f16528,f300])).

fof(f300,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f299])).

fof(f16794,plain,
    ( spl5_28
    | spl5_180
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f342,f163,f16792,f250])).

fof(f16792,plain,
    ( spl5_180
  <=> ! [X4] :
        ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X4,sK1))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(u1_struct_0(sK0),X4,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f342,plain,
    ( ! [X4] :
        ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X4,sK1))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(u1_struct_0(sK0),X4,sK1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f335,f221])).

fof(f16790,plain,
    ( spl5_166
    | ~ spl5_179
    | spl5_177 ),
    inference(avatar_split_clause,[],[f16783,f16780,f16788,f16745])).

fof(f16745,plain,
    ( spl5_166
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f16788,plain,
    ( spl5_179
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).

fof(f16780,plain,
    ( spl5_177
  <=> ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f16783,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK3(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_177 ),
    inference(resolution,[],[f16781,f16593])).

fof(f16593,plain,(
    ! [X19,X20] :
      ( r1_tarski(sK3(X19),X20)
      | ~ r1_tarski(X19,k1_zfmisc_1(X20))
      | v1_xboole_0(X19) ) ),
    inference(resolution,[],[f16528,f90])).

fof(f16781,plain,
    ( ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK3(k1_xboole_0))
    | ~ spl5_177 ),
    inference(avatar_component_clause,[],[f16780])).

fof(f16782,plain,
    ( ~ spl5_177
    | spl5_160
    | spl5_87
    | ~ spl5_88
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f16637,f12612,f6561,f6544,f16723,f16780])).

fof(f12612,plain,
    ( spl5_134
  <=> ! [X314] :
        ( m1_subset_1(X314,u1_struct_0(sK0))
        | ~ m1_subset_1(X314,sK3(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f16637,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK3(k1_xboole_0))
    | ~ spl5_87
    | ~ spl5_88
    | ~ spl5_134 ),
    inference(subsumption_resolution,[],[f16636,f6545])).

fof(f16636,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK3(k1_xboole_0))
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_88
    | ~ spl5_134 ),
    inference(superposition,[],[f16619,f6562])).

fof(f16619,plain,
    ( ! [X78] :
        ( m1_subset_1(sK3(X78),u1_struct_0(sK0))
        | ~ r1_tarski(X78,sK3(k1_xboole_0))
        | v1_xboole_0(X78) )
    | ~ spl5_134 ),
    inference(resolution,[],[f16528,f12613])).

fof(f12613,plain,
    ( ! [X314] :
        ( ~ m1_subset_1(X314,sK3(k1_xboole_0))
        | m1_subset_1(X314,u1_struct_0(sK0)) )
    | ~ spl5_134 ),
    inference(avatar_component_clause,[],[f12612])).

fof(f16775,plain,
    ( spl5_156
    | ~ spl5_175
    | spl5_160
    | ~ spl5_38
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f16635,f12612,f299,f16723,f16773,f16711])).

fof(f16773,plain,
    ( spl5_175
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f16635,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK3(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38
    | ~ spl5_134 ),
    inference(superposition,[],[f16619,f300])).

fof(f16768,plain,
    ( spl5_166
    | ~ spl5_173
    | spl5_171 ),
    inference(avatar_split_clause,[],[f16761,f16758,f16766,f16745])).

fof(f16766,plain,
    ( spl5_173
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f16758,plain,
    ( spl5_171
  <=> ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f16761,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_171 ),
    inference(resolution,[],[f16759,f16593])).

fof(f16759,plain,
    ( ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK2)
    | ~ spl5_171 ),
    inference(avatar_component_clause,[],[f16758])).

fof(f16760,plain,
    ( ~ spl5_171
    | spl5_160
    | ~ spl5_60
    | spl5_87
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f16632,f6561,f6544,f3302,f16723,f16758])).

fof(f16632,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK2)
    | ~ spl5_60
    | ~ spl5_87
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f16631,f6545])).

fof(f16631,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_60
    | ~ spl5_88 ),
    inference(superposition,[],[f16616,f6562])).

fof(f16753,plain,
    ( spl5_166
    | ~ spl5_169
    | spl5_165 ),
    inference(avatar_split_clause,[],[f16740,f16737,f16751,f16745])).

fof(f16751,plain,
    ( spl5_169
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f16737,plain,
    ( spl5_165
  <=> ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f16740,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_165 ),
    inference(resolution,[],[f16738,f16593])).

fof(f16738,plain,
    ( ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK1)
    | ~ spl5_165 ),
    inference(avatar_component_clause,[],[f16737])).

fof(f16739,plain,
    ( ~ spl5_165
    | spl5_160
    | ~ spl5_54
    | spl5_87
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f16627,f6561,f6544,f3064,f16723,f16737])).

fof(f16627,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK1)
    | ~ spl5_54
    | ~ spl5_87
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f16626,f6545])).

fof(f16626,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),sK1)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_54
    | ~ spl5_88 ),
    inference(superposition,[],[f16615,f6562])).

fof(f16732,plain,
    ( spl5_156
    | ~ spl5_163
    | spl5_160
    | ~ spl5_38
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f16630,f3302,f299,f16723,f16730,f16711])).

fof(f16730,plain,
    ( spl5_163
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f16630,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK2)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38
    | ~ spl5_60 ),
    inference(superposition,[],[f16616,f300])).

fof(f16725,plain,
    ( spl5_156
    | ~ spl5_159
    | spl5_160
    | ~ spl5_38
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f16625,f3064,f299,f16723,f16717,f16711])).

fof(f16717,plain,
    ( spl5_159
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f16625,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK1)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38
    | ~ spl5_54 ),
    inference(superposition,[],[f16615,f300])).

fof(f12770,plain,
    ( ~ spl5_153
    | spl5_68
    | spl5_154
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f5614,f5604,f12768,f3473,f12762])).

fof(f12762,plain,
    ( spl5_153
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f12768,plain,
    ( spl5_154
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f5604,plain,
    ( spl5_80
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f5614,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl5_80 ),
    inference(resolution,[],[f5605,f221])).

fof(f5605,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0))
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f5604])).

fof(f12757,plain,
    ( ~ spl5_149
    | spl5_68
    | spl5_150
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f5599,f5589,f12755,f3473,f12749])).

fof(f12749,plain,
    ( spl5_149
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f12755,plain,
    ( spl5_150
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f5589,plain,
    ( spl5_76
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f5599,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK1))))
    | ~ spl5_76 ),
    inference(resolution,[],[f5590,f221])).

fof(f5590,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f5589])).

fof(f12744,plain,
    ( spl5_28
    | spl5_146
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f459,f170,f12742,f250])).

fof(f12742,plain,
    ( spl5_146
  <=> ! [X6] :
        ( v1_xboole_0(k3_xboole_0(sK2,X6))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f459,plain,
    ( ! [X6] :
        ( v1_xboole_0(k3_xboole_0(sK2,X6))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,X6)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f450,f221])).

fof(f12740,plain,
    ( spl5_28
    | spl5_144
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f413,f163,f12738,f250])).

fof(f12738,plain,
    ( spl5_144
  <=> ! [X6] :
        ( v1_xboole_0(k3_xboole_0(sK1,X6))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f413,plain,
    ( ! [X6] :
        ( v1_xboole_0(k3_xboole_0(sK1,X6))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,X6)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f389,f221])).

fof(f12724,plain,
    ( spl5_142
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f12645,f12637,f1735,f170,f163,f114,f107,f12722])).

fof(f12637,plain,
    ( spl5_136
  <=> v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f12645,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_136 ),
    inference(subsumption_resolution,[],[f12641,f450])).

fof(f12641,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_136 ),
    inference(resolution,[],[f12638,f1741])).

fof(f12638,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_136 ),
    inference(avatar_component_clause,[],[f12637])).

fof(f12705,plain,
    ( spl5_140
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f12625,f12076,f1746,f170,f163,f114,f107,f12703])).

fof(f12076,plain,
    ( spl5_122
  <=> v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f12625,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f12618,f389])).

fof(f12618,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_122 ),
    inference(resolution,[],[f1752,f12077])).

fof(f12077,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f12076])).

fof(f12658,plain,
    ( spl5_138
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f12644,f12637,f1746,f170,f114,f107,f12656])).

fof(f12644,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_136 ),
    inference(subsumption_resolution,[],[f12640,f450])).

fof(f12640,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_136 ),
    inference(resolution,[],[f12638,f1752])).

fof(f12639,plain,
    ( spl5_136
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f12624,f12058,f1746,f170,f163,f114,f107,f12637])).

fof(f12624,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f12617,f389])).

fof(f12617,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_52
    | ~ spl5_120 ),
    inference(resolution,[],[f1752,f12059])).

fof(f12614,plain,
    ( spl5_94
    | spl5_134
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f11639,f8372,f12612,f6596])).

fof(f6596,plain,
    ( spl5_94
  <=> v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f11639,plain,
    ( ! [X314] :
        ( m1_subset_1(X314,u1_struct_0(sK0))
        | v1_xboole_0(sK3(k1_xboole_0))
        | ~ m1_subset_1(X314,sK3(k1_xboole_0)) )
    | ~ spl5_100 ),
    inference(resolution,[],[f8468,f83])).

fof(f8468,plain,
    ( ! [X212,X213] :
        ( ~ m1_subset_1(X212,k1_xboole_0)
        | m1_subset_1(X213,u1_struct_0(sK0))
        | v1_xboole_0(X212)
        | ~ m1_subset_1(X213,X212) )
    | ~ spl5_100 ),
    inference(superposition,[],[f235,f8373])).

fof(f12608,plain,
    ( ~ spl5_94
    | spl5_97 ),
    inference(avatar_contradiction_clause,[],[f12607])).

fof(f12607,plain,
    ( $false
    | ~ spl5_94
    | ~ spl5_97 ),
    inference(subsumption_resolution,[],[f12603,f6674])).

fof(f6674,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f6673])).

fof(f6673,plain,
    ( spl5_97
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f12603,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_94 ),
    inference(resolution,[],[f6597,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t6_boole)).

fof(f6597,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f6596])).

fof(f12606,plain,
    ( ~ spl5_36
    | ~ spl5_38
    | ~ spl5_94
    | spl5_97 ),
    inference(avatar_contradiction_clause,[],[f12605])).

fof(f12605,plain,
    ( $false
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_94
    | ~ spl5_97 ),
    inference(subsumption_resolution,[],[f12604,f6674])).

fof(f12604,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f12600,f300])).

fof(f12600,plain,
    ( sK3(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_36
    | ~ spl5_94 ),
    inference(resolution,[],[f6597,f293])).

fof(f293,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl5_36 ),
    inference(resolution,[],[f290,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t8_boole)).

fof(f290,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl5_36
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f12586,plain,
    ( spl5_130
    | spl5_132
    | spl5_95
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f9294,f8372,f6599,f12584,f12578])).

fof(f12578,plain,
    ( spl5_130
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f12584,plain,
    ( spl5_132
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(k1_xboole_0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f6599,plain,
    ( spl5_95
  <=> ~ v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f9294,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK3(k1_xboole_0)))),u1_struct_0(sK0))
    | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_xboole_0))))
    | ~ spl5_95
    | ~ spl5_100 ),
    inference(resolution,[],[f8561,f5562])).

fof(f5562,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f3047,f83])).

fof(f3047,plain,(
    ! [X185,X186] :
      ( ~ m1_subset_1(X185,sK3(k1_zfmisc_1(X186)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X186)))
      | m1_subset_1(X185,X186) ) ),
    inference(resolution,[],[f235,f83])).

fof(f8561,plain,
    ( ! [X294] :
        ( ~ m1_subset_1(X294,sK3(k1_xboole_0))
        | m1_subset_1(X294,u1_struct_0(sK0)) )
    | ~ spl5_95
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f8560,f6600])).

fof(f6600,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f6599])).

fof(f8560,plain,
    ( ! [X294] :
        ( v1_xboole_0(sK3(k1_xboole_0))
        | ~ m1_subset_1(X294,sK3(k1_xboole_0))
        | m1_subset_1(X294,u1_struct_0(sK0)) )
    | ~ spl5_100 ),
    inference(forward_demodulation,[],[f8511,f8373])).

fof(f8511,plain,
    ( ! [X294] :
        ( ~ m1_subset_1(X294,sK3(k1_xboole_0))
        | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X294,u1_struct_0(sK0)) )
    | ~ spl5_100 ),
    inference(superposition,[],[f3047,f8373])).

fof(f12404,plain,
    ( ~ spl5_127
    | spl5_68
    | spl5_128
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f8877,f8873,f12402,f3473,f12396])).

fof(f12396,plain,
    ( spl5_127
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f12402,plain,
    ( spl5_128
  <=> v1_xboole_0(sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f8873,plain,
    ( spl5_118
  <=> m1_subset_1(sK3(sK3(k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f8877,plain,
    ( v1_xboole_0(sK3(sK3(k1_xboole_0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_xboole_0)))
    | ~ spl5_118 ),
    inference(resolution,[],[f8874,f221])).

fof(f8874,plain,
    ( m1_subset_1(sK3(sK3(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f8873])).

fof(f12381,plain,
    ( spl5_124
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f12082,f12076,f1735,f163,f114,f107,f12379])).

fof(f12082,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f12079,f389])).

fof(f12079,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_122 ),
    inference(resolution,[],[f12077,f1741])).

fof(f12078,plain,
    ( spl5_122
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f12064,f12058,f1735,f163,f114,f107,f12076])).

fof(f12064,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f12061,f389])).

fof(f12061,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_120 ),
    inference(resolution,[],[f12059,f1741])).

fof(f12060,plain,
    ( spl5_120
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f12053,f1746,f1735,f170,f163,f114,f107,f12058])).

fof(f12053,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_50
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f12050,f171])).

fof(f12050,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_50
    | ~ spl5_52 ),
    inference(resolution,[],[f1741,f1747])).

fof(f8875,plain,
    ( spl5_118
    | spl5_95
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8563,f8372,f6599,f8873])).

fof(f8563,plain,
    ( m1_subset_1(sK3(sK3(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl5_95
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f8562,f6600])).

fof(f8562,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | m1_subset_1(sK3(sK3(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl5_100 ),
    inference(forward_demodulation,[],[f8520,f8373])).

fof(f8520,plain,
    ( m1_subset_1(sK3(sK3(k1_xboole_0)),u1_struct_0(sK0))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_100 ),
    inference(superposition,[],[f5562,f8373])).

fof(f8626,plain,
    ( spl5_116
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8467,f8372,f8624])).

fof(f8624,plain,
    ( spl5_116
  <=> r1_tarski(sK3(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f8467,plain,
    ( r1_tarski(sK3(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_100 ),
    inference(superposition,[],[f199,f8373])).

fof(f199,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f90,f83])).

fof(f8617,plain,
    ( spl5_114
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8495,f8372,f8615])).

fof(f8615,plain,
    ( spl5_114
  <=> m1_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f8495,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_100 ),
    inference(superposition,[],[f2530,f8373])).

fof(f8607,plain,
    ( spl5_112
    | ~ spl5_46
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8403,f8372,f397,f8605])).

fof(f8605,plain,
    ( spl5_112
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f397,plain,
    ( spl5_46
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f8403,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_46
    | ~ spl5_100 ),
    inference(superposition,[],[f398,f8373])).

fof(f398,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f397])).

fof(f8600,plain,
    ( ~ spl5_111
    | spl5_33
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8394,f8372,f263,f8598])).

fof(f8598,plain,
    ( spl5_111
  <=> ~ m1_subset_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f263,plain,
    ( spl5_33
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f8394,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK2)
    | ~ spl5_33
    | ~ spl5_100 ),
    inference(superposition,[],[f264,f8373])).

fof(f264,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f263])).

fof(f8593,plain,
    ( ~ spl5_109
    | spl5_27
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8393,f8372,f244,f8591])).

fof(f8591,plain,
    ( spl5_109
  <=> ~ m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f244,plain,
    ( spl5_27
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f8393,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl5_27
    | ~ spl5_100 ),
    inference(superposition,[],[f245,f8373])).

fof(f245,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f8584,plain,
    ( spl5_106
    | ~ spl5_18
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8392,f8372,f170,f8582])).

fof(f8392,plain,
    ( m1_subset_1(sK2,k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_100 ),
    inference(superposition,[],[f171,f8373])).

fof(f8575,plain,
    ( spl5_104
    | ~ spl5_16
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f8391,f8372,f163,f8573])).

fof(f8391,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl5_16
    | ~ spl5_100 ),
    inference(superposition,[],[f164,f8373])).

fof(f8547,plain,
    ( spl5_43
    | ~ spl5_100 ),
    inference(avatar_contradiction_clause,[],[f8546])).

fof(f8546,plain,
    ( $false
    | ~ spl5_43
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f8395,f174])).

fof(f174,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f85,f79])).

fof(f79,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t2_boole)).

fof(f8395,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_43
    | ~ spl5_100 ),
    inference(superposition,[],[f325,f8373])).

fof(f325,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_43
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f8388,plain,
    ( spl5_28
    | spl5_102
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f448,f170,f8386,f250])).

fof(f8386,plain,
    ( spl5_102
  <=> ! [X6] :
        ( v1_xboole_0(k3_xboole_0(X6,sK2))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(X6,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f448,plain,
    ( ! [X6] :
        ( v1_xboole_0(k3_xboole_0(X6,sK2))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(X6,sK2)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f423,f221])).

fof(f8374,plain,
    ( spl5_100
    | ~ spl5_28
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f8365,f299,f289,f250,f8372])).

fof(f8365,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_28
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f8361,f300])).

fof(f8361,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_28
    | ~ spl5_36 ),
    inference(resolution,[],[f251,f293])).

fof(f251,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f8359,plain,
    ( spl5_28
    | spl5_98
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f387,f163,f8357,f250])).

fof(f8357,plain,
    ( spl5_98
  <=> ! [X6] :
        ( v1_xboole_0(k3_xboole_0(X6,sK1))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(X6,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f387,plain,
    ( ! [X6] :
        ( v1_xboole_0(k3_xboole_0(X6,sK1))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(X6,sK1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f369,f221])).

fof(f6675,plain,
    ( ~ spl5_97
    | spl5_89
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f6592,f6575,f6558,f6673])).

fof(f6558,plain,
    ( spl5_89
  <=> k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f6575,plain,
    ( spl5_90
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f6592,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl5_89
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f6559,f6576])).

fof(f6576,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f6575])).

fof(f6559,plain,
    ( k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f6558])).

fof(f6601,plain,
    ( ~ spl5_95
    | spl5_85
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f6594,f6575,f6538,f6599])).

fof(f6538,plain,
    ( spl5_85
  <=> ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f6594,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_85
    | ~ spl5_90 ),
    inference(forward_demodulation,[],[f6539,f6576])).

fof(f6539,plain,
    ( ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f6538])).

fof(f6591,plain,
    ( spl5_92
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f6582,f6561,f6589])).

fof(f6589,plain,
    ( spl5_92
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f6582,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_88 ),
    inference(superposition,[],[f83,f6562])).

fof(f6577,plain,
    ( spl5_90
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f6568,f6547,f299,f289,f6575])).

fof(f6547,plain,
    ( spl5_86
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f6568,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_86 ),
    inference(forward_demodulation,[],[f6564,f300])).

fof(f6564,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_36
    | ~ spl5_86 ),
    inference(resolution,[],[f6548,f293])).

fof(f6548,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f6547])).

fof(f6563,plain,
    ( spl5_88
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f6554,f6541,f299,f289,f6561])).

fof(f6541,plain,
    ( spl5_84
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f6554,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_84 ),
    inference(forward_demodulation,[],[f6550,f300])).

fof(f6550,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_36
    | ~ spl5_84 ),
    inference(resolution,[],[f6542,f293])).

fof(f6542,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f6541])).

fof(f6549,plain,
    ( spl5_84
    | spl5_86
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f6201,f135,f6547,f6541])).

fof(f135,plain,
    ( spl5_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f6201,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_8 ),
    inference(resolution,[],[f5571,f277])).

fof(f277,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_xboole_0)
        | v1_xboole_0(X2) )
    | ~ spl5_8 ),
    inference(resolution,[],[f272,f83])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f223,f91])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f222,f89])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f100,f136])).

fof(f136,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t5_subset)).

fof(f5571,plain,(
    ! [X12] :
      ( r1_tarski(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(X12)))),X12)
      | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(X12)))) ) ),
    inference(resolution,[],[f5562,f90])).

fof(f5612,plain,
    ( spl5_80
    | spl5_82
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f5582,f3302,f5610,f5604])).

fof(f5610,plain,
    ( spl5_82
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f5582,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0))
    | ~ spl5_60 ),
    inference(resolution,[],[f5562,f3303])).

fof(f5597,plain,
    ( spl5_76
    | spl5_78
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f5581,f3064,f5595,f5589])).

fof(f5595,plain,
    ( spl5_78
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f5581,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl5_54 ),
    inference(resolution,[],[f5562,f3065])).

fof(f3494,plain,
    ( ~ spl5_73
    | spl5_68
    | spl5_74
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f3461,f3324,f3492,f3473,f3486])).

fof(f3486,plain,
    ( spl5_73
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f3492,plain,
    ( spl5_74
  <=> v1_xboole_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f3324,plain,
    ( spl5_64
  <=> m1_subset_1(sK3(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f3461,plain,
    ( v1_xboole_0(sK3(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2))
    | ~ spl5_64 ),
    inference(resolution,[],[f3325,f221])).

fof(f3325,plain,
    ( m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f3324])).

fof(f3481,plain,
    ( ~ spl5_67
    | spl5_68
    | spl5_70
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3299,f3086,f3479,f3473,f3467])).

fof(f3467,plain,
    ( spl5_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f3479,plain,
    ( spl5_70
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f3086,plain,
    ( spl5_58
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f3299,plain,
    ( v1_xboole_0(sK3(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl5_58 ),
    inference(resolution,[],[f3087,f221])).

fof(f3087,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f3086])).

fof(f3384,plain,
    ( ~ spl5_12
    | spl5_49
    | ~ spl5_62 ),
    inference(avatar_contradiction_clause,[],[f3383])).

fof(f3383,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_49
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f3382,f3328])).

fof(f3328,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl5_12
    | ~ spl5_62 ),
    inference(superposition,[],[f150,f3317])).

fof(f3317,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f3316])).

fof(f3316,plain,
    ( spl5_62
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f3382,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ spl5_49
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f3339,f79])).

fof(f3339,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,k1_xboole_0),sK0)
    | ~ spl5_49
    | ~ spl5_62 ),
    inference(superposition,[],[f431,f3317])).

fof(f3374,plain,
    ( ~ spl5_12
    | spl5_21
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(avatar_contradiction_clause,[],[f3373])).

fof(f3373,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_21
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f3372,f3328])).

fof(f3372,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ spl5_21
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f3330,f406])).

fof(f406,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f400,f79])).

fof(f400,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl5_46 ),
    inference(resolution,[],[f398,f96])).

fof(f3330,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0),sK0)
    | ~ spl5_21
    | ~ spl5_62 ),
    inference(superposition,[],[f181,f3317])).

fof(f181,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_21
  <=> ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f3326,plain,
    ( spl5_64
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3319,f3302,f3324])).

fof(f3319,plain,
    ( m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_60 ),
    inference(resolution,[],[f3303,f83])).

fof(f3318,plain,
    ( spl5_62
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f3309,f299,f289,f269,f3316])).

fof(f269,plain,
    ( spl5_34
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f3309,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f3305,f300])).

fof(f3305,plain,
    ( sK2 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(resolution,[],[f270,f293])).

fof(f270,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f3304,plain,
    ( spl5_34
    | spl5_60
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f3046,f170,f3302,f269])).

fof(f3046,plain,
    ( ! [X184] :
        ( m1_subset_1(X184,u1_struct_0(sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X184,sK2) )
    | ~ spl5_18 ),
    inference(resolution,[],[f235,f171])).

fof(f3172,plain,
    ( ~ spl5_10
    | spl5_49
    | ~ spl5_56 ),
    inference(avatar_contradiction_clause,[],[f3171])).

fof(f3171,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_49
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f3170,f3090])).

fof(f3090,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl5_10
    | ~ spl5_56 ),
    inference(superposition,[],[f143,f3079])).

fof(f3079,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f3078])).

fof(f3078,plain,
    ( spl5_56
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f3170,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ spl5_49
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f3107,f183])).

fof(f183,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f86,f79])).

fof(f3107,plain,
    ( ~ v2_compts_1(k3_xboole_0(k1_xboole_0,sK2),sK0)
    | ~ spl5_49
    | ~ spl5_56 ),
    inference(superposition,[],[f431,f3079])).

fof(f3152,plain,
    ( ~ spl5_10
    | ~ spl5_18
    | spl5_21
    | ~ spl5_56 ),
    inference(avatar_contradiction_clause,[],[f3151])).

fof(f3151,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_21
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f3150,f3090])).

fof(f3150,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | ~ spl5_18
    | ~ spl5_21
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f3149,f183])).

fof(f3149,plain,
    ( ~ v2_compts_1(k3_xboole_0(k1_xboole_0,sK2),sK0)
    | ~ spl5_18
    | ~ spl5_21
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f3092,f360])).

fof(f3092,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),k1_xboole_0,sK2),sK0)
    | ~ spl5_21
    | ~ spl5_56 ),
    inference(superposition,[],[f181,f3079])).

fof(f3088,plain,
    ( spl5_58
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3081,f3064,f3086])).

fof(f3081,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_54 ),
    inference(resolution,[],[f3065,f83])).

fof(f3080,plain,
    ( spl5_56
    | ~ spl5_30
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f3071,f299,f289,f256,f3078])).

fof(f256,plain,
    ( spl5_30
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f3071,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_30
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f3067,f300])).

fof(f3067,plain,
    ( sK1 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_30
    | ~ spl5_36 ),
    inference(resolution,[],[f257,f293])).

fof(f257,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f256])).

fof(f3066,plain,
    ( spl5_30
    | spl5_54
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f3045,f163,f3064,f256])).

fof(f3045,plain,
    ( ! [X183] :
        ( m1_subset_1(X183,u1_struct_0(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X183,sK1) )
    | ~ spl5_16 ),
    inference(resolution,[],[f235,f164])).

fof(f1748,plain,
    ( spl5_52
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f1730,f170,f149,f121,f114,f107,f1746])).

fof(f121,plain,
    ( spl5_4
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1730,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1728,f171])).

fof(f1728,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(resolution,[],[f925,f150])).

fof(f925,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f924,f108])).

fof(f924,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f923,f115])).

fof(f923,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f81,f122])).

fof(f122,plain,
    ( v8_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t16_compts_1)).

fof(f1737,plain,
    ( spl5_50
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1729,f163,f142,f121,f114,f107,f1735])).

fof(f1729,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1727,f164])).

fof(f1727,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f925,f143])).

fof(f432,plain,
    ( ~ spl5_49
    | ~ spl5_18
    | spl5_21 ),
    inference(avatar_split_clause,[],[f421,f180,f170,f430])).

fof(f421,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(superposition,[],[f181,f360])).

fof(f399,plain,
    ( spl5_46
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f391,f163,f397])).

fof(f391,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(superposition,[],[f369,f183])).

fof(f330,plain,
    ( spl5_44
    | spl5_36
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f273,f135,f289,f328])).

fof(f328,plain,
    ( spl5_44
  <=> ! [X2] : ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f273,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X2,sK3(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl5_8 ),
    inference(resolution,[],[f223,f83])).

fof(f326,plain,
    ( ~ spl5_43
    | spl5_28
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f275,f163,f135,f250,f324])).

fof(f275,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(resolution,[],[f272,f164])).

fof(f312,plain,
    ( spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f305,f299,f310])).

fof(f310,plain,
    ( spl5_40
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f305,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38 ),
    inference(superposition,[],[f83,f300])).

fof(f301,plain,
    ( spl5_38
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f294,f289,f299])).

fof(f294,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_36 ),
    inference(resolution,[],[f290,f80])).

fof(f291,plain,
    ( spl5_36
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f281,f135,f289])).

fof(f281,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_8 ),
    inference(resolution,[],[f277,f199])).

fof(f271,plain,
    ( ~ spl5_33
    | spl5_28
    | spl5_34
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f238,f170,f269,f250,f263])).

fof(f238,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl5_18 ),
    inference(resolution,[],[f221,f171])).

fof(f258,plain,
    ( ~ spl5_27
    | spl5_28
    | spl5_30
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f237,f163,f256,f250,f244])).

fof(f237,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_16 ),
    inference(resolution,[],[f221,f164])).

fof(f215,plain,
    ( spl5_24
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f201,f170,f213])).

fof(f213,plain,
    ( spl5_24
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f201,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_18 ),
    inference(resolution,[],[f90,f171])).

fof(f208,plain,
    ( spl5_22
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f200,f163,f206])).

fof(f206,plain,
    ( spl5_22
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f200,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(resolution,[],[f90,f164])).

fof(f182,plain,(
    ~ spl5_21 ),
    inference(avatar_split_clause,[],[f76,f180])).

fof(f76,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_compts_1(X2,X0)
            & v2_compts_1(sK1,X0)
            & v8_pre_topc(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_compts_1(X2,X0)
          & v2_compts_1(X1,X0)
          & v8_pre_topc(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_compts_1(sK2,X0)
        & v2_compts_1(X1,X0)
        & v8_pre_topc(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',t20_compts_1)).

fof(f172,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f72,f170])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f165,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f71,f163])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f158,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f78,f156])).

fof(f156,plain,
    ( spl5_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f78,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',d2_xboole_0)).

fof(f151,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f75,f149])).

fof(f75,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f144,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f74,f142])).

fof(f74,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f137,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f102,f135])).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f77,f78])).

fof(f77,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',dt_o_0_0_xboole_0)).

fof(f130,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f101,f128])).

fof(f128,plain,
    ( spl5_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f101,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f67])).

fof(f67,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t20_compts_1.p',existence_l1_pre_topc)).

fof(f123,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f73,f121])).

fof(f73,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f116,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f70,f114])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f69,f107])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
