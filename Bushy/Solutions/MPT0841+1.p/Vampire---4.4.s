%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t52_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:11 EDT 2019

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 188 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  305 ( 548 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f113,f131,f141,f152,f174,f217,f258,f367,f403,f415,f4749,f4936,f5151,f5182,f5194,f5282])).

fof(f5282,plain,
    ( spl11_44
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f5280,f139,f129,f215])).

fof(f215,plain,
    ( spl11_44
  <=> sP7(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f129,plain,
    ( spl11_20
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f139,plain,
    ( spl11_22
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f5280,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(resolution,[],[f5259,f130])).

fof(f130,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f129])).

fof(f5259,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP7(sK4,X0,sK3) )
    | ~ spl11_22 ),
    inference(resolution,[],[f140,f52])).

fof(f52,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',d13_relat_1)).

fof(f140,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f5194,plain,
    ( ~ spl11_10
    | ~ spl11_12
    | spl11_15
    | ~ spl11_44 ),
    inference(avatar_contradiction_clause,[],[f5193])).

fof(f5193,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f5192,f5189])).

fof(f5189,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl11_10
    | ~ spl11_15 ),
    inference(forward_demodulation,[],[f170,f108])).

fof(f108,plain,
    ( ! [X1] : k7_relset_1(sK2,sK0,sK3,X1) = k9_relat_1(sK3,X1)
    | ~ spl11_10 ),
    inference(resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',redefinition_k7_relset_1)).

fof(f98,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl11_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f170,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl11_15
  <=> ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f5192,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl11_12
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f233,f112])).

fof(f112,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl11_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f233,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl11_44 ),
    inference(resolution,[],[f216,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f216,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f215])).

fof(f5182,plain,
    ( spl11_91
    | ~ spl11_688 ),
    inference(avatar_contradiction_clause,[],[f5181])).

fof(f5181,plain,
    ( $false
    | ~ spl11_91
    | ~ spl11_688 ),
    inference(subsumption_resolution,[],[f5161,f414])).

fof(f414,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl11_91 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl11_91
  <=> ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_91])])).

fof(f5161,plain,
    ( m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl11_688 ),
    inference(resolution,[],[f5150,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',t1_subset)).

fof(f5150,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | ~ spl11_688 ),
    inference(avatar_component_clause,[],[f5149])).

fof(f5149,plain,
    ( spl11_688
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_688])])).

fof(f5151,plain,
    ( spl11_688
    | ~ spl11_654 ),
    inference(avatar_split_clause,[],[f5117,f4934,f5149])).

fof(f4934,plain,
    ( spl11_654
  <=> r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_654])])).

fof(f5117,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | ~ spl11_654 ),
    inference(resolution,[],[f4935,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',t106_zfmisc_1)).

fof(f4935,plain,
    ( r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl11_654 ),
    inference(avatar_component_clause,[],[f4934])).

fof(f4936,plain,
    ( spl11_654
    | spl11_85
    | ~ spl11_612 ),
    inference(avatar_split_clause,[],[f4816,f4747,f401,f4934])).

fof(f401,plain,
    ( spl11_85
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_85])])).

fof(f4747,plain,
    ( spl11_612
  <=> m1_subset_1(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_612])])).

fof(f4816,plain,
    ( r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl11_85
    | ~ spl11_612 ),
    inference(subsumption_resolution,[],[f4815,f402])).

fof(f402,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | ~ spl11_85 ),
    inference(avatar_component_clause,[],[f401])).

fof(f4815,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl11_612 ),
    inference(resolution,[],[f4748,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',t2_subset)).

fof(f4748,plain,
    ( m1_subset_1(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl11_612 ),
    inference(avatar_component_clause,[],[f4747])).

fof(f4749,plain,
    ( spl11_612
    | ~ spl11_10
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f1441,f365,f97,f4747])).

fof(f365,plain,
    ( spl11_72
  <=> r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f1441,plain,
    ( m1_subset_1(k4_tarski(sK8(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl11_10
    | ~ spl11_72 ),
    inference(resolution,[],[f376,f98])).

fof(f376,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
        | m1_subset_1(k4_tarski(sK8(sK3,sK1,sK4),sK4),X4) )
    | ~ spl11_72 ),
    inference(resolution,[],[f366,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',t4_subset)).

fof(f366,plain,
    ( r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),sK3)
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f365])).

fof(f415,plain,
    ( ~ spl11_91
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f382,f365,f256,f172,f413])).

fof(f172,plain,
    ( spl11_30
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f256,plain,
    ( spl11_50
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f382,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f372,f257])).

fof(f257,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f256])).

fof(f372,plain,
    ( ~ r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl11_30
    | ~ spl11_72 ),
    inference(resolution,[],[f366,f173])).

fof(f173,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f172])).

fof(f403,plain,
    ( ~ spl11_85
    | ~ spl11_10
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f395,f365,f97,f401])).

fof(f395,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | ~ spl11_10
    | ~ spl11_72 ),
    inference(resolution,[],[f375,f98])).

fof(f375,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
        | ~ v1_xboole_0(X3) )
    | ~ spl11_72 ),
    inference(resolution,[],[f366,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',t5_subset)).

fof(f367,plain,
    ( spl11_72
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f231,f215,f365])).

fof(f231,plain,
    ( r2_hidden(k4_tarski(sK8(sK3,sK1,sK4),sK4),sK3)
    | ~ spl11_44 ),
    inference(resolution,[],[f216,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(k4_tarski(sK8(X0,X1,X3),X3),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f258,plain,
    ( spl11_50
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f232,f215,f256])).

fof(f232,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ spl11_44 ),
    inference(resolution,[],[f216,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(sK8(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f217,plain,
    ( spl11_44
    | ~ spl11_12
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f209,f150,f111,f215])).

fof(f150,plain,
    ( spl11_24
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f209,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl11_12
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f202,f112])).

fof(f202,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl11_24 ),
    inference(resolution,[],[f151,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | sP7(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f150])).

fof(f174,plain,
    ( ~ spl11_15
    | spl11_30 ),
    inference(avatar_split_clause,[],[f40,f172,f169])).

fof(f40,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',t52_relset_1)).

fof(f152,plain,
    ( spl11_24
    | ~ spl11_10
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f142,f115,f97,f150])).

fof(f115,plain,
    ( spl11_14
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f142,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl11_10
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f116,f108])).

fof(f116,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f141,plain,
    ( spl11_14
    | spl11_22 ),
    inference(avatar_split_clause,[],[f42,f139,f115])).

fof(f42,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f131,plain,
    ( spl11_14
    | spl11_20 ),
    inference(avatar_split_clause,[],[f43,f129,f115])).

fof(f43,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( spl11_12
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f106,f97,f111])).

fof(f106,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_10 ),
    inference(resolution,[],[f98,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t52_relset_1.p',cc1_relset_1)).

fof(f99,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
