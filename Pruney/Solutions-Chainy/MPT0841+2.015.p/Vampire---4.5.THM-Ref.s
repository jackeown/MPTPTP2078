%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 146 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  262 ( 467 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f92,f98,f104,f108,f147,f156,f236,f243,f253])).

fof(f253,plain,
    ( ~ spl10_9
    | ~ spl10_10
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_10
    | spl10_16 ),
    inference(subsumption_resolution,[],[f250,f97])).

fof(f97,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_9
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f250,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl10_10
    | spl10_16 ),
    inference(resolution,[],[f244,f103])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl10_10
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_16 ),
    inference(resolution,[],[f154,f28])).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f154,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl10_16
  <=> sP7(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f243,plain,
    ( spl10_8
    | ~ spl10_13
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl10_8
    | ~ spl10_13
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f241,f155])).

fof(f155,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f241,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | spl10_8
    | ~ spl10_13 ),
    inference(resolution,[],[f91,f149])).

fof(f149,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k9_relat_1(sK3,X3))
        | ~ sP7(X2,X3,sK3) )
    | ~ spl10_13 ),
    inference(resolution,[],[f126,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f91,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl10_8
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f236,plain,
    ( ~ spl10_5
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f234,f155])).

fof(f234,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | ~ sP7(sK4,sK1,sK3)
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(resolution,[],[f195,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
        | ~ sP7(sK4,X0,sK3) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ sP7(sK4,X0,sK3)
        | ~ sP7(sK4,X0,sK3)
        | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(resolution,[],[f185,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK4),sK2)
        | ~ sP7(sK4,X0,sK3)
        | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) )
    | ~ spl10_6 ),
    inference(resolution,[],[f175,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
        | ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
        | ~ sP7(sK4,X0,sK3) )
    | ~ spl10_6 ),
    inference(resolution,[],[f174,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X3),X3),X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f174,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f18,f80])).

fof(f80,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl10_6
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f18,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f185,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK8(sK3,X1,X0),sK2)
        | ~ sP7(X0,X1,sK3) )
    | ~ spl10_5 ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f75,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK8(sK3,X2,X3),X3),k2_zfmisc_1(sK2,sK0))
        | ~ sP7(X3,X2,sK3) )
    | ~ spl10_5 ),
    inference(resolution,[],[f73,f29])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f156,plain,
    ( spl10_16
    | ~ spl10_8
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f150,f125,f89,f153])).

fof(f150,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl10_8
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f141,f126])).

fof(f141,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | sP7(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f147,plain,
    ( ~ spl10_5
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl10_5
    | spl10_13 ),
    inference(subsumption_resolution,[],[f144,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f144,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl10_5
    | spl10_13 ),
    inference(resolution,[],[f133,f71])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl10_13 ),
    inference(resolution,[],[f127,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f127,plain,
    ( ~ v1_relat_1(sK3)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f108,plain,
    ( ~ spl10_5
    | ~ spl10_6
    | spl10_8 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8 ),
    inference(subsumption_resolution,[],[f106,f71])).

fof(f106,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_6
    | spl10_8 ),
    inference(subsumption_resolution,[],[f105,f91])).

fof(f105,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_6 ),
    inference(superposition,[],[f80,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f104,plain,
    ( spl10_10
    | spl10_6 ),
    inference(avatar_split_clause,[],[f99,f78,f101])).

fof(f99,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | spl10_6 ),
    inference(subsumption_resolution,[],[f20,f79])).

fof(f79,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f20,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f98,plain,
    ( spl10_9
    | spl10_6 ),
    inference(avatar_split_clause,[],[f93,f78,f95])).

fof(f93,plain,
    ( r2_hidden(sK5,sK1)
    | spl10_6 ),
    inference(subsumption_resolution,[],[f21,f79])).

fof(f21,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,
    ( ~ spl10_8
    | ~ spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f87,f78,f69,f89])).

fof(f87,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f86,f71])).

fof(f86,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl10_6 ),
    inference(superposition,[],[f79,f42])).

fof(f72,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f23,f69])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:18:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (25320)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (25312)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (25323)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (25315)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (25315)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (25328)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (25313)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (25319)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (25316)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (25329)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f72,f92,f98,f104,f108,f147,f156,f236,f243,f253])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    ~spl10_9 | ~spl10_10 | spl10_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f252])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    $false | (~spl10_9 | ~spl10_10 | spl10_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f250,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    r2_hidden(sK5,sK1) | ~spl10_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl10_9 <=> r2_hidden(sK5,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    ~r2_hidden(sK5,sK1) | (~spl10_10 | spl10_16)),
% 0.22/0.50    inference(resolution,[],[f244,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl10_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl10_10 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_16),
% 0.22/0.50    inference(resolution,[],[f154,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ~sP7(sK4,sK1,sK3) | spl10_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl10_16 <=> sP7(sK4,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    spl10_8 | ~spl10_13 | ~spl10_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f242])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    $false | (spl10_8 | ~spl10_13 | ~spl10_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f241,f155])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    sP7(sK4,sK1,sK3) | ~spl10_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    ~sP7(sK4,sK1,sK3) | (spl10_8 | ~spl10_13)),
% 0.22/0.50    inference(resolution,[],[f91,f149])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(X2,k9_relat_1(sK3,X3)) | ~sP7(X2,X3,sK3)) ) | ~spl10_13),
% 0.22/0.50    inference(resolution,[],[f126,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    v1_relat_1(sK3) | ~spl10_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl10_13 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | spl10_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl10_8 <=> r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    ~spl10_5 | ~spl10_6 | ~spl10_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    $false | (~spl10_5 | ~spl10_6 | ~spl10_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f234,f155])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ~sP7(sK4,sK1,sK3) | (~spl10_5 | ~spl10_6)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f233])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    ~sP7(sK4,sK1,sK3) | ~sP7(sK4,sK1,sK3) | (~spl10_5 | ~spl10_6)),
% 0.22/0.50    inference(resolution,[],[f195,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~sP7(X3,X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK8(sK3,X0,sK4),sK1) | ~sP7(sK4,X0,sK3)) ) | (~spl10_5 | ~spl10_6)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ( ! [X0] : (~sP7(sK4,X0,sK3) | ~sP7(sK4,X0,sK3) | ~r2_hidden(sK8(sK3,X0,sK4),sK1)) ) | (~spl10_5 | ~spl10_6)),
% 0.22/0.50    inference(resolution,[],[f185,f176])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK8(sK3,X0,sK4),sK2) | ~sP7(sK4,X0,sK3) | ~r2_hidden(sK8(sK3,X0,sK4),sK1)) ) | ~spl10_6),
% 0.22/0.50    inference(resolution,[],[f175,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK4),sK2) | ~r2_hidden(sK8(sK3,X0,sK4),sK1) | ~sP7(sK4,X0,sK3)) ) | ~spl10_6),
% 0.22/0.50    inference(resolution,[],[f174,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X3),X3),X0) | ~sP7(X3,X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl10_6),
% 0.22/0.50    inference(subsumption_resolution,[],[f18,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~spl10_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl10_6 <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK8(sK3,X1,X0),sK2) | ~sP7(X0,X1,sK3)) ) | ~spl10_5),
% 0.22/0.50    inference(resolution,[],[f75,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK8(sK3,X2,X3),X3),k2_zfmisc_1(sK2,sK0)) | ~sP7(X3,X2,sK3)) ) | ~spl10_5),
% 0.22/0.50    inference(resolution,[],[f73,f29])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k2_zfmisc_1(sK2,sK0))) ) | ~spl10_5),
% 0.22/0.50    inference(resolution,[],[f71,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl10_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl10_16 | ~spl10_8 | ~spl10_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f150,f125,f89,f153])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    sP7(sK4,sK1,sK3) | (~spl10_8 | ~spl10_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f141,f126])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    sP7(sK4,sK1,sK3) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.22/0.50    inference(resolution,[],[f90,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | sP7(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~spl10_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ~spl10_5 | spl10_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    $false | (~spl10_5 | spl10_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f144,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl10_5 | spl10_13)),
% 0.22/0.50    inference(resolution,[],[f133,f71])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl10_13),
% 0.22/0.50    inference(resolution,[],[f127,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl10_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~spl10_5 | ~spl10_6 | spl10_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    $false | (~spl10_5 | ~spl10_6 | spl10_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f71])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | (~spl10_6 | spl10_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f105,f91])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_6),
% 0.22/0.50    inference(superposition,[],[f80,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl10_10 | spl10_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f99,f78,f101])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK5,sK4),sK3) | spl10_6),
% 0.22/0.50    inference(subsumption_resolution,[],[f20,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | spl10_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl10_9 | spl10_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f93,f78,f95])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    r2_hidden(sK5,sK1) | spl10_6),
% 0.22/0.51    inference(subsumption_resolution,[],[f21,f79])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ~spl10_8 | ~spl10_5 | spl10_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f87,f78,f69,f89])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | (~spl10_5 | spl10_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f86,f71])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | spl10_6),
% 0.22/0.51    inference(superposition,[],[f79,f42])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl10_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f69])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (25315)------------------------------
% 0.22/0.51  % (25315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25315)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (25315)Memory used [KB]: 10746
% 0.22/0.51  % (25315)Time elapsed: 0.063 s
% 0.22/0.51  % (25315)------------------------------
% 0.22/0.51  % (25315)------------------------------
% 0.22/0.51  % (25311)Success in time 0.137 s
%------------------------------------------------------------------------------
