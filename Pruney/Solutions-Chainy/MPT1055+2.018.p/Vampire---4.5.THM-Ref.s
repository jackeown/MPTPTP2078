%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 240 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  423 ( 771 expanded)
%              Number of equality atoms :   51 (  66 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f91,f96,f111,f116,f135,f161,f167,f177,f184,f201,f209,f233,f251,f263,f270,f387,f405,f462,f471])).

fof(f471,plain,
    ( ~ spl5_17
    | spl5_19
    | ~ spl5_39 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl5_17
    | spl5_19
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f468,f188])).

fof(f188,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl5_19
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f468,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_17
    | ~ spl5_39 ),
    inference(resolution,[],[f467,f172])).

fof(f172,plain,
    ( ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_17
  <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f467,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0)
        | r1_tarski(k9_relat_1(sK2,sK3),X0) )
    | ~ spl5_39 ),
    inference(superposition,[],[f49,f461])).

fof(f461,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK4)) = k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl5_39
  <=> k9_relat_1(sK2,k10_relat_1(sK2,sK4)) = k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f462,plain,
    ( spl5_39
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f409,f402,f459])).

fof(f402,plain,
    ( spl5_34
  <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f409,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK4)) = k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_34 ),
    inference(resolution,[],[f404,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f404,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f402])).

fof(f405,plain,
    ( spl5_34
    | ~ spl5_18
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f400,f256,f174,f402])).

fof(f174,plain,
    ( spl5_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f256,plain,
    ( spl5_26
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f400,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl5_18
    | ~ spl5_26 ),
    inference(resolution,[],[f391,f175])).

fof(f175,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,k10_relat_1(sK2,sK4))) )
    | ~ spl5_26 ),
    inference(resolution,[],[f257,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f257,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f387,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22
    | spl5_26 ),
    inference(subsumption_resolution,[],[f382,f258])).

fof(f258,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f382,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(resolution,[],[f187,f303])).

fof(f303,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X1)
        | r1_tarski(sK3,k10_relat_1(sK2,X1)) )
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_22 ),
    inference(resolution,[],[f261,f110])).

fof(f110,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_8
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl5_1
    | ~ spl5_18
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f260,f205])).

fof(f205,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl5_22
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl5_1
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f80,f175])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f68,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f187,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f270,plain,
    ( ~ spl5_9
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f264,f257])).

fof(f264,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f246,f187])).

fof(f246,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f245,f120])).

fof(f120,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)
    | ~ spl5_9 ),
    inference(resolution,[],[f115,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f245,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f33,f121])).

fof(f121,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(sK0,sK1,sK2,X1)
    | ~ spl5_9 ),
    inference(resolution,[],[f115,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f33,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f263,plain,
    ( ~ spl5_9
    | ~ spl5_16
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_16
    | spl5_26 ),
    inference(subsumption_resolution,[],[f247,f258])).

fof(f247,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f169,f121])).

fof(f169,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_16 ),
    inference(resolution,[],[f166,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k8_relset_1(sK0,sK1,sK2,sK4)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k8_relset_1(sK0,sK1,sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f251,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_10
    | spl5_19 ),
    inference(subsumption_resolution,[],[f249,f188])).

fof(f249,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f130,f120])).

fof(f130,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_10
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f233,plain,
    ( spl5_2
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl5_2
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f218,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f218,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_21 ),
    inference(superposition,[],[f73,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl5_21
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f209,plain,
    ( spl5_22
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f206,f194,f158,f203])).

fof(f158,plain,
    ( spl5_15
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f194,plain,
    ( spl5_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f206,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(superposition,[],[f196,f160])).

fof(f160,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f196,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f201,plain,
    ( spl5_20
    | spl5_21
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f126,f113,f93,f198,f194])).

fof(f93,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f123,f95])).

fof(f95,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f115,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f184,plain,
    ( ~ spl5_9
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl5_9
    | spl5_18 ),
    inference(subsumption_resolution,[],[f182,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f182,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_9
    | spl5_18 ),
    inference(resolution,[],[f178,f115])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_18 ),
    inference(resolution,[],[f176,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f176,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( spl5_17
    | ~ spl5_18
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f81,f66,f174,f171])).

fof(f81,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f167,plain,
    ( spl5_16
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f145,f132,f164])).

fof(f132,plain,
    ( spl5_11
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f145,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k8_relset_1(sK0,sK1,sK2,sK4)))
    | ~ spl5_11 ),
    inference(resolution,[],[f134,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f134,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f161,plain,
    ( spl5_15
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f124,f113,f158])).

fof(f124,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f115,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f135,plain,
    ( spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f32,f132,f128])).

fof(f32,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f38,f113])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f111,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f103,f88,f108])).

fof(f88,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f103,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f90,f47])).

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f37,f93])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.42  % (643)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (631)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (633)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (655)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (631)Refutation not found, incomplete strategy% (631)------------------------------
% 0.20/0.51  % (631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (631)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (631)Memory used [KB]: 10618
% 0.20/0.51  % (631)Time elapsed: 0.088 s
% 0.20/0.51  % (631)------------------------------
% 0.20/0.51  % (631)------------------------------
% 0.20/0.51  % (630)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (636)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (641)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (638)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (632)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (661)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (634)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (642)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (661)Refutation not found, incomplete strategy% (661)------------------------------
% 0.20/0.52  % (661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (661)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (661)Memory used [KB]: 10618
% 0.20/0.52  % (661)Time elapsed: 0.079 s
% 0.20/0.52  % (661)------------------------------
% 0.20/0.52  % (661)------------------------------
% 0.20/0.52  % (656)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (640)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.53  % (637)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.53  % (657)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (633)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f472,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f69,f74,f91,f96,f111,f116,f135,f161,f167,f177,f184,f201,f209,f233,f251,f263,f270,f387,f405,f462,f471])).
% 0.20/0.53  fof(f471,plain,(
% 0.20/0.53    ~spl5_17 | spl5_19 | ~spl5_39),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f470])).
% 0.20/0.53  fof(f470,plain,(
% 0.20/0.53    $false | (~spl5_17 | spl5_19 | ~spl5_39)),
% 0.20/0.53    inference(subsumption_resolution,[],[f468,f188])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f186])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    spl5_19 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.53  fof(f468,plain,(
% 0.20/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_17 | ~spl5_39)),
% 0.20/0.53    inference(resolution,[],[f467,f172])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl5_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    spl5_17 <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.53  fof(f467,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0) | r1_tarski(k9_relat_1(sK2,sK3),X0)) ) | ~spl5_39),
% 0.20/0.53    inference(superposition,[],[f49,f461])).
% 0.20/0.53  fof(f461,plain,(
% 0.20/0.53    k9_relat_1(sK2,k10_relat_1(sK2,sK4)) = k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl5_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f459])).
% 0.20/0.53  fof(f459,plain,(
% 0.20/0.53    spl5_39 <=> k9_relat_1(sK2,k10_relat_1(sK2,sK4)) = k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.53  fof(f462,plain,(
% 0.20/0.53    spl5_39 | ~spl5_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f409,f402,f459])).
% 0.20/0.53  fof(f402,plain,(
% 0.20/0.53    spl5_34 <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.20/0.53  fof(f409,plain,(
% 0.20/0.53    k9_relat_1(sK2,k10_relat_1(sK2,sK4)) = k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl5_34),
% 0.20/0.53    inference(resolution,[],[f404,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.53  fof(f404,plain,(
% 0.20/0.53    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl5_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f402])).
% 0.20/0.53  fof(f405,plain,(
% 0.20/0.53    spl5_34 | ~spl5_18 | ~spl5_26),
% 0.20/0.53    inference(avatar_split_clause,[],[f400,f256,f174,f402])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    spl5_18 <=> v1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    spl5_26 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.53  fof(f400,plain,(
% 0.20/0.53    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | (~spl5_18 | ~spl5_26)),
% 0.20/0.53    inference(resolution,[],[f391,f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    v1_relat_1(sK2) | ~spl5_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f174])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,k10_relat_1(sK2,sK4)))) ) | ~spl5_26),
% 0.20/0.53    inference(resolution,[],[f257,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f256])).
% 0.20/0.53  fof(f387,plain,(
% 0.20/0.53    ~spl5_1 | ~spl5_8 | ~spl5_18 | ~spl5_19 | ~spl5_22 | spl5_26),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f386])).
% 0.20/0.53  fof(f386,plain,(
% 0.20/0.53    $false | (~spl5_1 | ~spl5_8 | ~spl5_18 | ~spl5_19 | ~spl5_22 | spl5_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f382,f258])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f256])).
% 0.20/0.53  fof(f382,plain,(
% 0.20/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_1 | ~spl5_8 | ~spl5_18 | ~spl5_19 | ~spl5_22)),
% 0.20/0.53    inference(resolution,[],[f187,f303])).
% 0.20/0.53  fof(f303,plain,(
% 0.20/0.53    ( ! [X1] : (~r1_tarski(k9_relat_1(sK2,sK3),X1) | r1_tarski(sK3,k10_relat_1(sK2,X1))) ) | (~spl5_1 | ~spl5_8 | ~spl5_18 | ~spl5_22)),
% 0.20/0.53    inference(resolution,[],[f261,f110])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    r1_tarski(sK3,sK0) | ~spl5_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl5_8 <=> r1_tarski(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | (~spl5_1 | ~spl5_18 | ~spl5_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f260,f205])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | ~spl5_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f203])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    spl5_22 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | (~spl5_1 | ~spl5_18)),
% 0.20/0.53    inference(subsumption_resolution,[],[f80,f175])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl5_1),
% 0.20/0.53    inference(resolution,[],[f68,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    v1_funct_1(sK2) | ~spl5_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl5_1 <=> v1_funct_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f186])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    ~spl5_9 | ~spl5_19 | ~spl5_26),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f269])).
% 0.20/0.53  fof(f269,plain,(
% 0.20/0.53    $false | (~spl5_9 | ~spl5_19 | ~spl5_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f264,f257])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | ~spl5_19)),
% 0.20/0.53    inference(subsumption_resolution,[],[f246,f187])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_9),
% 0.20/0.53    inference(forward_demodulation,[],[f245,f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) ) | ~spl5_9),
% 0.20/0.53    inference(resolution,[],[f115,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f113])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_9),
% 0.20/0.53    inference(forward_demodulation,[],[f33,f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X1] : (k10_relat_1(sK2,X1) = k8_relset_1(sK0,sK1,sK2,X1)) ) | ~spl5_9),
% 0.20/0.53    inference(resolution,[],[f115,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f14])).
% 0.20/0.53  fof(f14,conjecture,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    ~spl5_9 | ~spl5_16 | spl5_26),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    $false | (~spl5_9 | ~spl5_16 | spl5_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f247,f258])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | ~spl5_16)),
% 0.20/0.53    inference(forward_demodulation,[],[f169,f121])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_16),
% 0.20/0.53    inference(resolution,[],[f166,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k8_relset_1(sK0,sK1,sK2,sK4))) | ~spl5_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f164])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    spl5_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k8_relset_1(sK0,sK1,sK2,sK4)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    ~spl5_9 | ~spl5_10 | spl5_19),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f250])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    $false | (~spl5_9 | ~spl5_10 | spl5_19)),
% 0.20/0.53    inference(subsumption_resolution,[],[f249,f188])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | ~spl5_10)),
% 0.20/0.53    inference(forward_demodulation,[],[f130,f120])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    spl5_10 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    spl5_2 | ~spl5_21),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f232])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    $false | (spl5_2 | ~spl5_21)),
% 0.20/0.53    inference(subsumption_resolution,[],[f218,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_21)),
% 0.20/0.53    inference(superposition,[],[f73,f200])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~spl5_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f198])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    spl5_21 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1) | spl5_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl5_2 <=> v1_xboole_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    spl5_22 | ~spl5_15 | ~spl5_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f206,f194,f158,f203])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    spl5_15 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    spl5_20 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | (~spl5_15 | ~spl5_20)),
% 0.20/0.53    inference(superposition,[],[f196,f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f158])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f194])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl5_20 | spl5_21 | ~spl5_6 | ~spl5_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f126,f113,f93,f198,f194])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_6 | ~spl5_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f123,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl5_9),
% 0.20/0.53    inference(resolution,[],[f115,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    ~spl5_9 | spl5_18),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    $false | (~spl5_9 | spl5_18)),
% 0.20/0.53    inference(subsumption_resolution,[],[f182,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_9 | spl5_18)),
% 0.20/0.53    inference(resolution,[],[f178,f115])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_18),
% 0.20/0.53    inference(resolution,[],[f176,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    ~v1_relat_1(sK2) | spl5_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f174])).
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    spl5_17 | ~spl5_18 | ~spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f81,f66,f174,f171])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl5_1),
% 0.20/0.53    inference(resolution,[],[f68,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    spl5_16 | ~spl5_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f145,f132,f164])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    spl5_11 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k8_relset_1(sK0,sK1,sK2,sK4))) | ~spl5_11),
% 0.20/0.53    inference(resolution,[],[f134,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f132])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    spl5_15 | ~spl5_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f124,f113,f158])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_9),
% 0.20/0.53    inference(resolution,[],[f115,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl5_10 | spl5_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f32,f132,f128])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    spl5_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f113])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl5_8 | ~spl5_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f103,f88,f108])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    r1_tarski(sK3,sK0) | ~spl5_5),
% 0.20/0.53    inference(resolution,[],[f90,f47])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    spl5_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f37,f93])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl5_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f35,f88])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ~spl5_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f39,f71])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f36,f66])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (633)------------------------------
% 0.20/0.53  % (633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (633)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (633)Memory used [KB]: 10874
% 0.20/0.53  % (633)Time elapsed: 0.104 s
% 0.20/0.53  % (633)------------------------------
% 0.20/0.53  % (633)------------------------------
% 0.20/0.53  % (629)Success in time 0.175 s
%------------------------------------------------------------------------------
