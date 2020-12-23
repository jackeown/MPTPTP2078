%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 264 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  454 ( 834 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f130,f135,f140,f150,f163,f171,f188,f200,f256,f360,f385,f408,f434,f477,f483,f491,f537,f802,f815])).

fof(f815,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f814])).

fof(f814,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(subsumption_resolution,[],[f803,f162])).

fof(f162,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_10
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f803,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f479,f139])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f479,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(superposition,[],[f145,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f145,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_8
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f802,plain,
    ( ~ spl6_5
    | ~ spl6_35
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_35
    | spl6_40 ),
    inference(subsumption_resolution,[],[f799,f433])).

fof(f433,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl6_35
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f799,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl6_5
    | spl6_40 ),
    inference(resolution,[],[f568,f129])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f568,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
        | ~ r1_tarski(X4,k1_relat_1(sK2)) )
    | spl6_40 ),
    inference(resolution,[],[f538,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f538,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | spl6_40 ),
    inference(resolution,[],[f536,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f536,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl6_40
  <=> r1_tarski(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f537,plain,
    ( ~ spl6_40
    | ~ spl6_1
    | ~ spl6_10
    | spl6_11
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f497,f185,f168,f160,f97,f534])).

fof(f97,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f168,plain,
    ( spl6_11
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f185,plain,
    ( spl6_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f497,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_10
    | spl6_11
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f493,f161])).

fof(f161,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f493,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl6_1
    | spl6_11
    | ~ spl6_14 ),
    inference(resolution,[],[f169,f275])).

fof(f275,plain,
    ( ! [X6,X5] :
        ( r1_tarski(X5,k10_relat_1(sK2,X6))
        | ~ r1_tarski(k9_relat_1(sK2,X5),X6)
        | ~ r1_tarski(X5,k1_relat_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f115,f186])).

fof(f186,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f115,plain,
    ( ! [X6,X5] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X5,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X5),X6)
        | r1_tarski(X5,k10_relat_1(sK2,X6)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f99,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f169,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f491,plain,
    ( ~ spl6_7
    | spl6_9
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl6_7
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f489,f139])).

fof(f489,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f488,f170])).

fof(f170,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f488,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_9 ),
    inference(superposition,[],[f148,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f148,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_9
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f483,plain,
    ( ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f478,f145])).

fof(f478,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f55,f149])).

fof(f149,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f55,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

% (28147)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(f477,plain,
    ( spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f472,f170])).

fof(f472,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_10
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(resolution,[],[f307,f183])).

fof(f183,plain,
    ( ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_13
  <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0) )
    | spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f302,f186])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0)
        | ~ v1_relat_1(sK2) )
    | spl6_10 ),
    inference(resolution,[],[f164,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl6_10 ),
    inference(resolution,[],[f162,f90])).

fof(f434,plain,
    ( spl6_35
    | ~ spl6_14
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f416,f382,f185,f431])).

fof(f382,plain,
    ( spl6_32
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f416,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f415,f186])).

fof(f415,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_32 ),
    inference(superposition,[],[f67,f384])).

fof(f384,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f382])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f408,plain,
    ( spl6_15
    | ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl6_15
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f399,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f399,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | spl6_15
    | ~ spl6_31 ),
    inference(superposition,[],[f199,f359])).

fof(f359,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl6_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f199,plain,
    ( ~ r1_tarski(sK1,sK5(sK1))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_15
  <=> r1_tarski(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f385,plain,
    ( spl6_32
    | ~ spl6_7
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f363,f353,f137,f382])).

fof(f353,plain,
    ( spl6_30
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f363,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl6_7
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f361,f139])).

fof(f361,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_30 ),
    inference(superposition,[],[f355,f92])).

fof(f355,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f353])).

fof(f360,plain,
    ( spl6_30
    | spl6_31
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f238,f137,f132,f97,f357,f353])).

fof(f132,plain,
    ( spl6_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f238,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f237,f139])).

fof(f237,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(resolution,[],[f116,f134])).

fof(f134,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f116,plain,
    ( ! [X8,X7] :
        ( ~ v1_funct_2(sK2,X7,X8)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_xboole_0 = X8
        | k8_relset_1(X7,X8,sK2,X8) = X7 )
    | ~ spl6_1 ),
    inference(resolution,[],[f99,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f256,plain,
    ( ~ spl6_7
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl6_7
    | spl6_14 ),
    inference(subsumption_resolution,[],[f253,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f253,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_7
    | spl6_14 ),
    inference(resolution,[],[f189,f139])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_14 ),
    inference(resolution,[],[f187,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f187,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f200,plain,
    ( ~ spl6_15
    | spl6_2 ),
    inference(avatar_split_clause,[],[f177,f102,f197])).

fof(f102,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f177,plain,
    ( ~ r1_tarski(sK1,sK5(sK1))
    | spl6_2 ),
    inference(resolution,[],[f141,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | spl6_2 ),
    inference(resolution,[],[f119,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f119,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK1) )
    | spl6_2 ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f188,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f112,f97,f185,f182])).

fof(f112,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f99,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f171,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f158,f147,f137,f168])).

fof(f158,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f157,f139])).

fof(f157,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(superposition,[],[f149,f92])).

fof(f163,plain,
    ( ~ spl6_10
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f156,f143,f137,f160])).

fof(f156,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f155,f139])).

fof(f155,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_8 ),
    inference(superposition,[],[f144,f91])).

fof(f144,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f150,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f54,f147,f143])).

fof(f54,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f140,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f60,f137])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f135,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f59,f132])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f130,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f57,f127])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f61,f102])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f58,f97])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (28150)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (28167)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (28159)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (28148)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (28160)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (28155)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (28151)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (28149)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (28152)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (28161)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (28150)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f816,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f100,f105,f130,f135,f140,f150,f163,f171,f188,f200,f256,f360,f385,f408,f434,f477,f483,f491,f537,f802,f815])).
% 0.21/0.50  fof(f815,plain,(
% 0.21/0.50    ~spl6_7 | ~spl6_8 | spl6_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f814])).
% 0.21/0.50  fof(f814,plain,(
% 0.21/0.50    $false | (~spl6_7 | ~spl6_8 | spl6_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f803,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl6_10 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f803,plain,(
% 0.21/0.50    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_7 | ~spl6_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f479,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f479,plain,(
% 0.21/0.50    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_8),
% 0.21/0.50    inference(superposition,[],[f145,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl6_8 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f802,plain,(
% 0.21/0.50    ~spl6_5 | ~spl6_35 | spl6_40),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f801])).
% 0.21/0.50  fof(f801,plain,(
% 0.21/0.50    $false | (~spl6_5 | ~spl6_35 | spl6_40)),
% 0.21/0.50    inference(subsumption_resolution,[],[f799,f433])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl6_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f431])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    spl6_35 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.50  fof(f799,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k1_relat_1(sK2)) | (~spl6_5 | spl6_40)),
% 0.21/0.50    inference(resolution,[],[f568,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f568,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_subset_1(sK3,k1_zfmisc_1(X4)) | ~r1_tarski(X4,k1_relat_1(sK2))) ) | spl6_40),
% 0.21/0.50    inference(resolution,[],[f538,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f538,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK3,X0) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | spl6_40),
% 0.21/0.50    inference(resolution,[],[f536,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f536,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k1_relat_1(sK2)) | spl6_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f534])).
% 0.21/0.50  fof(f534,plain,(
% 0.21/0.50    spl6_40 <=> r1_tarski(sK3,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.50  fof(f537,plain,(
% 0.21/0.50    ~spl6_40 | ~spl6_1 | ~spl6_10 | spl6_11 | ~spl6_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f497,f185,f168,f160,f97,f534])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl6_11 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl6_14 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.50  fof(f497,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl6_1 | ~spl6_10 | spl6_11 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f493,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f493,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl6_1 | spl6_11 | ~spl6_14)),
% 0.21/0.50    inference(resolution,[],[f169,f275])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ( ! [X6,X5] : (r1_tarski(X5,k10_relat_1(sK2,X6)) | ~r1_tarski(k9_relat_1(sK2,X5),X6) | ~r1_tarski(X5,k1_relat_1(sK2))) ) | (~spl6_1 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f115,f186])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f185])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X6,X5] : (~v1_relat_1(sK2) | ~r1_tarski(X5,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X5),X6) | r1_tarski(X5,k10_relat_1(sK2,X6))) ) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f99,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f491,plain,(
% 0.21/0.50    ~spl6_7 | spl6_9 | ~spl6_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f490])).
% 0.21/0.50  fof(f490,plain,(
% 0.21/0.50    $false | (~spl6_7 | spl6_9 | ~spl6_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f489,f139])).
% 0.21/0.50  fof(f489,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl6_9 | ~spl6_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f488,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f488,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_9),
% 0.21/0.50    inference(superposition,[],[f148,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl6_9 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f483,plain,(
% 0.21/0.50    ~spl6_8 | ~spl6_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f482])).
% 0.21/0.50  fof(f482,plain,(
% 0.21/0.50    $false | (~spl6_8 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f478,f145])).
% 0.21/0.50  fof(f478,plain,(
% 0.21/0.50    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_9),
% 0.21/0.50    inference(subsumption_resolution,[],[f55,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f25])).
% 0.21/0.50  % (28147)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  fof(f25,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f24])).
% 0.21/0.50  fof(f24,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 0.21/0.50  fof(f477,plain,(
% 0.21/0.50    spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f476])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    $false | (spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f472,f170])).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (spl6_10 | ~spl6_13 | ~spl6_14)),
% 0.21/0.50    inference(resolution,[],[f307,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl6_13 <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0)) ) | (spl6_10 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f302,f186])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0) | ~v1_relat_1(sK2)) ) | spl6_10),
% 0.21/0.50    inference(resolution,[],[f164,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK3),X0) | ~r1_tarski(X0,sK4)) ) | spl6_10),
% 0.21/0.50    inference(resolution,[],[f162,f90])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    spl6_35 | ~spl6_14 | ~spl6_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f416,f382,f185,f431])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    spl6_32 <=> sK0 = k10_relat_1(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    r1_tarski(sK0,k1_relat_1(sK2)) | (~spl6_14 | ~spl6_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f415,f186])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl6_32),
% 0.21/0.50    inference(superposition,[],[f67,f384])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    sK0 = k10_relat_1(sK2,sK1) | ~spl6_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f382])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    spl6_15 | ~spl6_31),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f407])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    $false | (spl6_15 | ~spl6_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f399,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | (spl6_15 | ~spl6_31)),
% 0.21/0.50    inference(superposition,[],[f199,f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl6_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f357])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    spl6_31 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK5(sK1)) | spl6_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl6_15 <=> r1_tarski(sK1,sK5(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    spl6_32 | ~spl6_7 | ~spl6_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f363,f353,f137,f382])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    spl6_30 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    sK0 = k10_relat_1(sK2,sK1) | (~spl6_7 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f361,f139])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    sK0 = k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_30),
% 0.21/0.50    inference(superposition,[],[f355,f92])).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl6_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f353])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    spl6_30 | spl6_31 | ~spl6_1 | ~spl6_6 | ~spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f238,f137,f132,f97,f357,f353])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl6_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl6_1 | ~spl6_6 | ~spl6_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f237,f139])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl6_1 | ~spl6_6)),
% 0.21/0.50    inference(resolution,[],[f116,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X8,X7] : (~v1_funct_2(sK2,X7,X8) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k1_xboole_0 = X8 | k8_relset_1(X7,X8,sK2,X8) = X7) ) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f99,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ~spl6_7 | spl6_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f255])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    $false | (~spl6_7 | spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f253,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_7 | spl6_14)),
% 0.21/0.50    inference(resolution,[],[f189,f139])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_14),
% 0.21/0.50    inference(resolution,[],[f187,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f185])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~spl6_15 | spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f177,f102,f197])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl6_2 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK5(sK1)) | spl6_2),
% 0.21/0.50    inference(resolution,[],[f141,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0)) ) | spl6_2),
% 0.21/0.50    inference(resolution,[],[f119,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK1)) ) | spl6_2),
% 0.21/0.50    inference(resolution,[],[f104,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl6_13 | ~spl6_14 | ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f112,f97,f185,f182])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X2] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f99,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    spl6_11 | ~spl6_7 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f147,f137,f168])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f139])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_9),
% 0.21/0.50    inference(superposition,[],[f149,f92])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~spl6_10 | ~spl6_7 | spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f156,f143,f137,f160])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_7 | spl6_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f155,f139])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_8),
% 0.21/0.50    inference(superposition,[],[f144,f91])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f143])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl6_8 | spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f147,f143])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f137])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f132])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f127])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f102])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f97])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28150)------------------------------
% 0.21/0.50  % (28150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28150)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28150)Memory used [KB]: 11001
% 0.21/0.50  % (28150)Time elapsed: 0.072 s
% 0.21/0.50  % (28150)------------------------------
% 0.21/0.50  % (28150)------------------------------
% 0.21/0.50  % (28156)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (28146)Success in time 0.147 s
%------------------------------------------------------------------------------
