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
% DateTime   : Thu Dec  3 12:57:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 175 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  273 ( 510 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f68,f73,f89,f94,f98,f133,f147,f158,f170,f225,f261,f395,f415,f430])).

fof(f430,plain,
    ( spl10_21
    | ~ spl10_39 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | spl10_21
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f427,f260])).

fof(f260,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl10_21
  <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f427,plain,
    ( m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_39 ),
    inference(resolution,[],[f414,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
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

fof(f414,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl10_39
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f415,plain,
    ( spl10_39
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f404,f393,f413])).

fof(f393,plain,
    ( spl10_36
  <=> r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f404,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_36 ),
    inference(resolution,[],[f394,f23])).

fof(f23,plain,(
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

fof(f394,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f393])).

fof(f395,plain,
    ( spl10_36
    | ~ spl10_2
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f203,f156,f47,f393])).

fof(f47,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f156,plain,
    ( spl10_18
  <=> r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f203,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl10_2
    | ~ spl10_18 ),
    inference(resolution,[],[f157,f52])).

fof(f52,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k2_zfmisc_1(sK2,sK0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f157,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f261,plain,
    ( ~ spl10_21
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f221,f156,f96,f92,f259])).

fof(f92,plain,
    ( spl10_10
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f96,plain,
    ( spl10_11
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f221,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f220,f97])).

fof(f97,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f220,plain,
    ( ~ r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_10
    | ~ spl10_18 ),
    inference(resolution,[],[f93,f157])).

fof(f93,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f225,plain,
    ( spl10_7
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f210,f145,f87,f66,f54,f71])).

fof(f71,plain,
    ( spl10_7
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f54,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f66,plain,
    ( spl10_6
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f87,plain,
    ( spl10_9
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f145,plain,
    ( spl10_16
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f210,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(resolution,[],[f197,f67])).

fof(f67,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_3
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f196,f55])).

fof(f55,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f192,f146])).

fof(f146,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,k1_relat_1(sK3))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_9 ),
    inference(resolution,[],[f88,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f170,plain,
    ( ~ spl10_7
    | ~ spl10_2
    | spl10_4 ),
    inference(avatar_split_clause,[],[f105,f58,f47,f71])).

fof(f58,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f105,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_2
    | spl10_4 ),
    inference(forward_demodulation,[],[f90,f51])).

fof(f51,plain,
    ( ! [X0] : k7_relset_1(sK2,sK0,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl10_2 ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f90,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f158,plain,
    ( spl10_18
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f129,f71,f54,f156])).

fof(f129,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3)
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f125,f55])).

fof(f125,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f72,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f147,plain,
    ( spl10_16
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f138,f131,f145])).

fof(f131,plain,
    ( spl10_14
  <=> sP8(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f138,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl10_14 ),
    inference(resolution,[],[f132,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ sP8(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ sP8(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f132,plain,
    ( sP8(sK5,sK3)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl10_14
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f109,f87,f131])).

fof(f109,plain,
    ( sP8(sK5,sK3)
    | ~ spl10_9 ),
    inference(resolution,[],[f88,f31])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP8(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f98,plain,
    ( spl10_11
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f81,f71,f54,f96])).

fof(f81,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f76,f55])).

fof(f76,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f72,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,
    ( ~ spl10_4
    | spl10_10 ),
    inference(avatar_split_clause,[],[f17,f92,f58])).

fof(f17,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f89,plain,
    ( spl10_4
    | spl10_9 ),
    inference(avatar_split_clause,[],[f19,f87,f58])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,
    ( spl10_7
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f69,f58,f47,f71])).

fof(f69,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f59,f51])).

fof(f59,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,
    ( spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f20,f66,f58])).

fof(f20,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f50,f47,f54])).

fof(f50,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (10724)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (10721)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (10711)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (10712)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (10722)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (10719)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (10710)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (10708)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (10714)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.53  % (10708)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (10720)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (10715)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.53  % (10728)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.36/0.53  % (10727)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.36/0.53  % (10713)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.36/0.54  % (10709)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f431,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f49,f56,f68,f73,f89,f94,f98,f133,f147,f158,f170,f225,f261,f395,f415,f430])).
% 1.36/0.54  fof(f430,plain,(
% 1.36/0.54    spl10_21 | ~spl10_39),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f429])).
% 1.36/0.54  fof(f429,plain,(
% 1.36/0.54    $false | (spl10_21 | ~spl10_39)),
% 1.36/0.54    inference(subsumption_resolution,[],[f427,f260])).
% 1.36/0.54  fof(f260,plain,(
% 1.36/0.54    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | spl10_21),
% 1.36/0.54    inference(avatar_component_clause,[],[f259])).
% 1.36/0.54  fof(f259,plain,(
% 1.36/0.54    spl10_21 <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.36/0.54  fof(f427,plain,(
% 1.36/0.54    m1_subset_1(sK6(sK4,sK1,sK3),sK2) | ~spl10_39),
% 1.36/0.54    inference(resolution,[],[f414,f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.36/0.54  fof(f414,plain,(
% 1.36/0.54    r2_hidden(sK6(sK4,sK1,sK3),sK2) | ~spl10_39),
% 1.36/0.54    inference(avatar_component_clause,[],[f413])).
% 1.36/0.54  fof(f413,plain,(
% 1.36/0.54    spl10_39 <=> r2_hidden(sK6(sK4,sK1,sK3),sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 1.36/0.54  fof(f415,plain,(
% 1.36/0.54    spl10_39 | ~spl10_36),
% 1.36/0.54    inference(avatar_split_clause,[],[f404,f393,f413])).
% 1.36/0.54  fof(f393,plain,(
% 1.36/0.54    spl10_36 <=> r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),k2_zfmisc_1(sK2,sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 1.36/0.54  fof(f404,plain,(
% 1.36/0.54    r2_hidden(sK6(sK4,sK1,sK3),sK2) | ~spl10_36),
% 1.36/0.54    inference(resolution,[],[f394,f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.36/0.54  fof(f394,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),k2_zfmisc_1(sK2,sK0)) | ~spl10_36),
% 1.36/0.54    inference(avatar_component_clause,[],[f393])).
% 1.36/0.54  fof(f395,plain,(
% 1.36/0.54    spl10_36 | ~spl10_2 | ~spl10_18),
% 1.36/0.54    inference(avatar_split_clause,[],[f203,f156,f47,f393])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.36/0.54  fof(f156,plain,(
% 1.36/0.54    spl10_18 <=> r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.36/0.54  fof(f203,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),k2_zfmisc_1(sK2,sK0)) | (~spl10_2 | ~spl10_18)),
% 1.36/0.54    inference(resolution,[],[f157,f52])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,k2_zfmisc_1(sK2,sK0))) ) | ~spl10_2),
% 1.36/0.54    inference(resolution,[],[f48,f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f47])).
% 1.36/0.54  fof(f157,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3) | ~spl10_18),
% 1.36/0.54    inference(avatar_component_clause,[],[f156])).
% 1.36/0.54  fof(f261,plain,(
% 1.36/0.54    ~spl10_21 | ~spl10_10 | ~spl10_11 | ~spl10_18),
% 1.36/0.54    inference(avatar_split_clause,[],[f221,f156,f96,f92,f259])).
% 1.36/0.54  fof(f92,plain,(
% 1.36/0.54    spl10_10 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.36/0.54  fof(f96,plain,(
% 1.36/0.54    spl10_11 <=> r2_hidden(sK6(sK4,sK1,sK3),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.36/0.54  fof(f221,plain,(
% 1.36/0.54    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_10 | ~spl10_11 | ~spl10_18)),
% 1.36/0.54    inference(subsumption_resolution,[],[f220,f97])).
% 1.36/0.54  fof(f97,plain,(
% 1.36/0.54    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~spl10_11),
% 1.36/0.54    inference(avatar_component_clause,[],[f96])).
% 1.36/0.54  fof(f220,plain,(
% 1.36/0.54    ~r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_10 | ~spl10_18)),
% 1.36/0.54    inference(resolution,[],[f93,f157])).
% 1.36/0.54  fof(f93,plain,(
% 1.36/0.54    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_10),
% 1.36/0.54    inference(avatar_component_clause,[],[f92])).
% 1.36/0.54  fof(f225,plain,(
% 1.36/0.54    spl10_7 | ~spl10_3 | ~spl10_6 | ~spl10_9 | ~spl10_16),
% 1.36/0.54    inference(avatar_split_clause,[],[f210,f145,f87,f66,f54,f71])).
% 1.36/0.54  fof(f71,plain,(
% 1.36/0.54    spl10_7 <=> r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    spl10_3 <=> v1_relat_1(sK3)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    spl10_6 <=> r2_hidden(sK5,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.36/0.54  fof(f87,plain,(
% 1.36/0.54    spl10_9 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.36/0.54  fof(f145,plain,(
% 1.36/0.54    spl10_16 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.36/0.54  fof(f210,plain,(
% 1.36/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | (~spl10_3 | ~spl10_6 | ~spl10_9 | ~spl10_16)),
% 1.36/0.54    inference(resolution,[],[f197,f67])).
% 1.36/0.54  fof(f67,plain,(
% 1.36/0.54    r2_hidden(sK5,sK1) | ~spl10_6),
% 1.36/0.54    inference(avatar_component_clause,[],[f66])).
% 1.36/0.54  fof(f197,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | (~spl10_3 | ~spl10_9 | ~spl10_16)),
% 1.36/0.54    inference(subsumption_resolution,[],[f196,f55])).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    v1_relat_1(sK3) | ~spl10_3),
% 1.36/0.54    inference(avatar_component_clause,[],[f54])).
% 1.36/0.54  fof(f196,plain,(
% 1.36/0.54    ( ! [X0] : (~v1_relat_1(sK3) | ~r2_hidden(sK5,X0) | r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | (~spl10_9 | ~spl10_16)),
% 1.36/0.54    inference(subsumption_resolution,[],[f192,f146])).
% 1.36/0.54  fof(f146,plain,(
% 1.36/0.54    r2_hidden(sK5,k1_relat_1(sK3)) | ~spl10_16),
% 1.36/0.54    inference(avatar_component_clause,[],[f145])).
% 1.36/0.54  fof(f192,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~r2_hidden(sK5,X0) | r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | ~spl10_9),
% 1.36/0.54    inference(resolution,[],[f88,f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,plain,(
% 1.36/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.36/0.54  fof(f88,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl10_9),
% 1.36/0.54    inference(avatar_component_clause,[],[f87])).
% 1.36/0.54  fof(f170,plain,(
% 1.36/0.54    ~spl10_7 | ~spl10_2 | spl10_4),
% 1.36/0.54    inference(avatar_split_clause,[],[f105,f58,f47,f71])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.36/0.54  fof(f105,plain,(
% 1.36/0.54    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | (~spl10_2 | spl10_4)),
% 1.36/0.54    inference(forward_demodulation,[],[f90,f51])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ( ! [X0] : (k7_relset_1(sK2,sK0,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl10_2),
% 1.36/0.54    inference(resolution,[],[f48,f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.36/0.54  fof(f90,plain,(
% 1.36/0.54    ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | spl10_4),
% 1.36/0.54    inference(avatar_component_clause,[],[f58])).
% 1.36/0.54  fof(f158,plain,(
% 1.36/0.54    spl10_18 | ~spl10_3 | ~spl10_7),
% 1.36/0.54    inference(avatar_split_clause,[],[f129,f71,f54,f156])).
% 1.36/0.54  fof(f129,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3) | (~spl10_3 | ~spl10_7)),
% 1.36/0.54    inference(subsumption_resolution,[],[f125,f55])).
% 1.36/0.54  fof(f125,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl10_7),
% 1.36/0.54    inference(resolution,[],[f72,f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~spl10_7),
% 1.36/0.54    inference(avatar_component_clause,[],[f71])).
% 1.36/0.54  fof(f147,plain,(
% 1.36/0.54    spl10_16 | ~spl10_14),
% 1.36/0.54    inference(avatar_split_clause,[],[f138,f131,f145])).
% 1.36/0.54  fof(f131,plain,(
% 1.36/0.54    spl10_14 <=> sP8(sK5,sK3)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.36/0.54  fof(f138,plain,(
% 1.36/0.54    r2_hidden(sK5,k1_relat_1(sK3)) | ~spl10_14),
% 1.36/0.54    inference(resolution,[],[f132,f41])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ( ! [X2,X0] : (~sP8(X2,X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.36/0.54    inference(equality_resolution,[],[f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~sP8(X2,X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.36/0.54  fof(f132,plain,(
% 1.36/0.54    sP8(sK5,sK3) | ~spl10_14),
% 1.36/0.54    inference(avatar_component_clause,[],[f131])).
% 1.36/0.54  fof(f133,plain,(
% 1.36/0.54    spl10_14 | ~spl10_9),
% 1.36/0.54    inference(avatar_split_clause,[],[f109,f87,f131])).
% 1.36/0.54  fof(f109,plain,(
% 1.36/0.54    sP8(sK5,sK3) | ~spl10_9),
% 1.36/0.54    inference(resolution,[],[f88,f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | sP8(X2,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f98,plain,(
% 1.36/0.54    spl10_11 | ~spl10_3 | ~spl10_7),
% 1.36/0.54    inference(avatar_split_clause,[],[f81,f71,f54,f96])).
% 1.36/0.54  fof(f81,plain,(
% 1.36/0.54    r2_hidden(sK6(sK4,sK1,sK3),sK1) | (~spl10_3 | ~spl10_7)),
% 1.36/0.54    inference(subsumption_resolution,[],[f76,f55])).
% 1.36/0.54  fof(f76,plain,(
% 1.36/0.54    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~v1_relat_1(sK3) | ~spl10_7),
% 1.36/0.54    inference(resolution,[],[f72,f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f94,plain,(
% 1.36/0.54    ~spl10_4 | spl10_10),
% 1.36/0.54    inference(avatar_split_clause,[],[f17,f92,f58])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,plain,(
% 1.36/0.54    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.36/0.54    inference(ennf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,plain,(
% 1.36/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 1.36/0.54    inference(pure_predicate_removal,[],[f9])).
% 1.36/0.54  fof(f9,negated_conjecture,(
% 1.36/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.36/0.54    inference(negated_conjecture,[],[f8])).
% 1.36/0.54  fof(f8,conjecture,(
% 1.36/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 1.36/0.54  fof(f89,plain,(
% 1.36/0.54    spl10_4 | spl10_9),
% 1.36/0.54    inference(avatar_split_clause,[],[f19,f87,f58])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    spl10_7 | ~spl10_2 | ~spl10_4),
% 1.36/0.54    inference(avatar_split_clause,[],[f69,f58,f47,f71])).
% 1.36/0.54  fof(f69,plain,(
% 1.36/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | (~spl10_2 | ~spl10_4)),
% 1.36/0.54    inference(forward_demodulation,[],[f59,f51])).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~spl10_4),
% 1.36/0.54    inference(avatar_component_clause,[],[f58])).
% 1.36/0.54  fof(f68,plain,(
% 1.36/0.54    spl10_4 | spl10_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f20,f66,f58])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    spl10_3 | ~spl10_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f50,f47,f54])).
% 1.36/0.54  fof(f50,plain,(
% 1.36/0.54    v1_relat_1(sK3) | ~spl10_2),
% 1.36/0.54    inference(resolution,[],[f48,f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    spl10_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f22,f47])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (10708)------------------------------
% 1.36/0.54  % (10708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (10708)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (10708)Memory used [KB]: 6396
% 1.36/0.54  % (10708)Time elapsed: 0.097 s
% 1.36/0.54  % (10708)------------------------------
% 1.36/0.54  % (10708)------------------------------
% 1.36/0.54  % (10718)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.49/0.55  % (10707)Success in time 0.187 s
%------------------------------------------------------------------------------
