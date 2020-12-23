%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 166 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 533 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f84,f108,f135,f145,f156,f164,f171,f208,f217,f223,f226,f258])).

fof(f258,plain,
    ( ~ spl10_8
    | spl10_11
    | ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl10_8
    | spl10_11
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f255,f107])).

fof(f107,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl10_8
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f255,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl10_11
    | ~ spl10_18 ),
    inference(resolution,[],[f235,f216])).

fof(f216,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl10_18
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_11 ),
    inference(resolution,[],[f143,f28])).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f143,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl10_11
  <=> sP7(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f226,plain,
    ( spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f224,f144])).

fof(f144,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f224,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | spl10_9
    | ~ spl10_10 ),
    inference(resolution,[],[f133,f158])).

fof(f158,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k10_relat_1(sK3,X3))
        | ~ sP7(X2,X3,sK3) )
    | ~ spl10_10 ),
    inference(resolution,[],[f139,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f139,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl10_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f133,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl10_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_9
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f223,plain,
    ( ~ spl10_5
    | spl10_6
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl10_5
    | spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f210,f134])).

fof(f134,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f210,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f209,f83])).

fof(f83,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f209,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl10_6 ),
    inference(superposition,[],[f91,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f91,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl10_6
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f217,plain,
    ( spl10_18
    | spl10_6 ),
    inference(avatar_split_clause,[],[f212,f90,f214])).

fof(f212,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | spl10_6 ),
    inference(subsumption_resolution,[],[f20,f91])).

fof(f20,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
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
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
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
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(f208,plain,
    ( ~ spl10_5
    | ~ spl10_11
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_11
    | spl10_13 ),
    inference(subsumption_resolution,[],[f206,f144])).

fof(f206,plain,
    ( ~ sP7(sK4,sK1,sK3)
    | ~ spl10_5
    | spl10_13 ),
    inference(resolution,[],[f173,f170])).

fof(f170,plain,
    ( ~ r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_13
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK8(sK3,X3,X2),sK2)
        | ~ sP7(X2,X3,sK3) )
    | ~ spl10_5 ),
    inference(resolution,[],[f147,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f147,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(X2,sK8(sK3,X3,X2)),k2_zfmisc_1(sK0,sK2))
        | ~ sP7(X2,X3,sK3) )
    | ~ spl10_5 ),
    inference(resolution,[],[f85,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK8(X0,X1,X3)),X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f171,plain,
    ( ~ spl10_13
    | spl10_1
    | spl10_12 ),
    inference(avatar_split_clause,[],[f165,f161,f52,f168])).

fof(f52,plain,
    ( spl10_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f161,plain,
    ( spl10_12
  <=> m1_subset_1(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f165,plain,
    ( ~ r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | spl10_1
    | spl10_12 ),
    inference(resolution,[],[f163,f72])).

fof(f72,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,sK2)
        | ~ r2_hidden(X1,sK2) )
    | spl10_1 ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f54,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f163,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( ~ spl10_12
    | ~ spl10_6
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f159,f142,f90,f161])).

fof(f159,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl10_6
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f151,f144])).

fof(f151,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ sP7(sK4,sK1,sK3)
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ sP7(sK4,sK1,sK3)
    | ~ sP7(sK4,sK1,sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f123,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
        | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
        | ~ sP7(sK4,X0,sK3) )
    | ~ spl10_6 ),
    inference(resolution,[],[f119,f29])).

fof(f119,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f18,f92])).

fof(f92,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f18,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f156,plain,
    ( ~ spl10_5
    | spl10_10 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl10_5
    | spl10_10 ),
    inference(subsumption_resolution,[],[f153,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | ~ spl10_5
    | spl10_10 ),
    inference(resolution,[],[f149,f83])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl10_10 ),
    inference(resolution,[],[f140,f27])).

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

fof(f140,plain,
    ( ~ v1_relat_1(sK3)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f145,plain,
    ( ~ spl10_10
    | spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f136,f132,f142,f138])).

fof(f136,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_9 ),
    inference(resolution,[],[f134,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP7(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f135,plain,
    ( spl10_9
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f110,f90,f81,f132])).

fof(f110,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f109,f83])).

fof(f109,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_6 ),
    inference(superposition,[],[f92,f45])).

fof(f108,plain,
    ( spl10_8
    | spl10_6 ),
    inference(avatar_split_clause,[],[f103,f90,f105])).

fof(f103,plain,
    ( r2_hidden(sK5,sK1)
    | spl10_6 ),
    inference(subsumption_resolution,[],[f21,f91])).

fof(f21,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f23,f81])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:50:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (17233)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (17224)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (17223)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (17231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (17225)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (17231)Refutation not found, incomplete strategy% (17231)------------------------------
% 0.21/0.47  % (17231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17231)Memory used [KB]: 1663
% 0.21/0.48  % (17231)Time elapsed: 0.053 s
% 0.21/0.48  % (17231)------------------------------
% 0.21/0.48  % (17231)------------------------------
% 0.21/0.48  % (17218)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (17232)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (17230)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17229)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (17221)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (17234)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (17219)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (17221)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f55,f84,f108,f135,f145,f156,f164,f171,f208,f217,f223,f226,f258])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ~spl10_8 | spl10_11 | ~spl10_18),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    $false | (~spl10_8 | spl10_11 | ~spl10_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f255,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    r2_hidden(sK5,sK1) | ~spl10_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl10_8 <=> r2_hidden(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~r2_hidden(sK5,sK1) | (spl10_11 | ~spl10_18)),
% 0.21/0.51    inference(resolution,[],[f235,f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    spl10_18 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_11),
% 0.21/0.51    inference(resolution,[],[f143,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X4,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~sP7(sK4,sK1,sK3) | spl10_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl10_11 <=> sP7(sK4,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    spl10_9 | ~spl10_10 | ~spl10_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    $false | (spl10_9 | ~spl10_10 | ~spl10_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f224,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    sP7(sK4,sK1,sK3) | ~spl10_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~sP7(sK4,sK1,sK3) | (spl10_9 | ~spl10_10)),
% 0.21/0.51    inference(resolution,[],[f133,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(X2,k10_relat_1(sK3,X3)) | ~sP7(X2,X3,sK3)) ) | ~spl10_10),
% 0.21/0.51    inference(resolution,[],[f139,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl10_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl10_10 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl10_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl10_9 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    ~spl10_5 | spl10_6 | ~spl10_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    $false | (~spl10_5 | spl10_6 | ~spl10_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_5 | spl10_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f209,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl10_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl10_6),
% 0.21/0.51    inference(superposition,[],[f91,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl10_6 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl10_18 | spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f212,f90,f214])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | spl10_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f20,f91])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ~spl10_5 | ~spl10_11 | spl10_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    $false | (~spl10_5 | ~spl10_11 | spl10_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f206,f144])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ~sP7(sK4,sK1,sK3) | (~spl10_5 | spl10_13)),
% 0.21/0.51    inference(resolution,[],[f173,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~r2_hidden(sK8(sK3,sK1,sK4),sK2) | spl10_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f168])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl10_13 <=> r2_hidden(sK8(sK3,sK1,sK4),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK8(sK3,X3,X2),sK2) | ~sP7(X2,X3,sK3)) ) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f147,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,sK8(sK3,X3,X2)),k2_zfmisc_1(sK0,sK2)) | ~sP7(X2,X3,sK3)) ) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f85,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK8(X0,X1,X3)),X0) | ~sP7(X3,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k2_zfmisc_1(sK0,sK2))) ) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f83,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~spl10_13 | spl10_1 | spl10_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f161,f52,f168])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl10_1 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl10_12 <=> m1_subset_1(sK8(sK3,sK1,sK4),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~r2_hidden(sK8(sK3,sK1,sK4),sK2) | (spl10_1 | spl10_12)),
% 0.21/0.51    inference(resolution,[],[f163,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(X1,sK2) | ~r2_hidden(X1,sK2)) ) | spl10_1),
% 0.21/0.51    inference(resolution,[],[f54,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl10_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f52])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | spl10_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~spl10_12 | ~spl10_6 | ~spl10_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f159,f142,f90,f161])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | (~spl10_6 | ~spl10_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f151,f144])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | ~sP7(sK4,sK1,sK3) | ~spl10_6),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | ~sP7(sK4,sK1,sK3) | ~sP7(sK4,sK1,sK3) | ~spl10_6),
% 0.21/0.51    inference(resolution,[],[f123,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~sP7(X3,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK8(sK3,X0,sK4),sK1) | ~m1_subset_1(sK8(sK3,X0,sK4),sK2) | ~sP7(sK4,X0,sK3)) ) | ~spl10_6),
% 0.21/0.51    inference(resolution,[],[f119,f29])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl10_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f18,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~spl10_5 | spl10_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    $false | (~spl10_5 | spl10_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | (~spl10_5 | spl10_10)),
% 0.21/0.51    inference(resolution,[],[f149,f83])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl10_10),
% 0.21/0.51    inference(resolution,[],[f140,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl10_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~spl10_10 | spl10_11 | ~spl10_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f132,f142,f138])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    sP7(sK4,sK1,sK3) | ~v1_relat_1(sK3) | ~spl10_9),
% 0.21/0.51    inference(resolution,[],[f134,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP7(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl10_9 | ~spl10_5 | ~spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f110,f90,f81,f132])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_5 | ~spl10_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f83])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_6),
% 0.21/0.51    inference(superposition,[],[f92,f45])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl10_8 | spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f90,f105])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    r2_hidden(sK5,sK1) | spl10_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f21,f91])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f81])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~spl10_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (17221)------------------------------
% 0.21/0.51  % (17221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17221)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (17221)Memory used [KB]: 10746
% 0.21/0.51  % (17221)Time elapsed: 0.095 s
% 0.21/0.51  % (17221)------------------------------
% 0.21/0.51  % (17221)------------------------------
% 0.21/0.51  % (17237)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (17220)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (17236)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (17222)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (17235)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (17238)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (17226)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (17228)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (17227)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (17217)Success in time 0.165 s
%------------------------------------------------------------------------------
