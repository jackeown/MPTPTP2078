%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:54 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 139 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  272 ( 457 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f86,f100,f104,f118,f124,f128,f154,f203,f288,f324,f329,f586,f592])).

fof(f592,plain,
    ( ~ spl11_13
    | ~ spl11_8
    | ~ spl11_28
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f588,f584,f279,f93,f121])).

fof(f121,plain,
    ( spl11_13
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f93,plain,
    ( spl11_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f279,plain,
    ( spl11_28
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f584,plain,
    ( spl11_44
  <=> ! [X0] :
        ( ~ r2_hidden(sK10(sK4,sK1,sK3),X0)
        | ~ r1_tarski(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f588,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl11_44 ),
    inference(resolution,[],[f585,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f585,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK4,sK1,sK3),X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f584])).

fof(f586,plain,
    ( ~ spl11_8
    | spl11_44
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(avatar_split_clause,[],[f576,f201,f121,f584,f93])).

fof(f201,plain,
    ( spl11_21
  <=> ! [X1] :
        ( ~ r2_hidden(sK10(sK4,X1,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
        | ~ m1_subset_1(sK10(sK4,X1,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f576,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
        | ~ r2_hidden(sK10(sK4,sK1,sK3),X0)
        | ~ r1_tarski(X0,sK2)
        | ~ v1_relat_1(sK3) )
    | ~ spl11_21 ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
        | ~ r2_hidden(sK10(sK4,sK1,sK3),X0)
        | ~ r1_tarski(X0,sK2)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) )
    | ~ spl11_21 ),
    inference(resolution,[],[f365,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f365,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK10(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK10(sK4,X0,sK3),X1)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl11_21 ),
    inference(resolution,[],[f224,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK10(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl11_21 ),
    inference(resolution,[],[f202,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f202,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK10(sK4,X1,sK3),sK2)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK10(sK4,X1,sK3),sK1) )
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f201])).

fof(f329,plain,
    ( ~ spl11_8
    | ~ spl11_12
    | spl11_13
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_12
    | spl11_13
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f95,f117,f153,f122,f51])).

fof(f51,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f122,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl11_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f153,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl11_16
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f117,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl11_12
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f95,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f324,plain,
    ( ~ spl11_5
    | ~ spl11_13
    | spl11_10 ),
    inference(avatar_split_clause,[],[f310,f106,f121,f75])).

fof(f75,plain,
    ( spl11_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f106,plain,
    ( spl11_10
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f310,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl11_10 ),
    inference(superposition,[],[f107,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f107,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | spl11_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f288,plain,
    ( ~ spl11_6
    | ~ spl11_8
    | spl11_28 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_8
    | spl11_28 ),
    inference(unit_resulting_resolution,[],[f95,f85,f281,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f281,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl11_28 ),
    inference(avatar_component_clause,[],[f279])).

fof(f85,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl11_6
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f203,plain,
    ( ~ spl11_8
    | spl11_21
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f157,f126,f201,f93])).

fof(f126,plain,
    ( spl11_14
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f157,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK10(sK4,X1,sK3),sK1)
        | ~ m1_subset_1(sK10(sK4,X1,sK3),sK2)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X1)) )
    | ~ spl11_14 ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f127,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f154,plain,
    ( spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f23,f151,f106])).

fof(f23,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f128,plain,
    ( ~ spl11_10
    | spl11_14 ),
    inference(avatar_split_clause,[],[f21,f126,f106])).

fof(f21,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f124,plain,
    ( ~ spl11_5
    | spl11_13
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f119,f106,f121,f75])).

fof(f119,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl11_10 ),
    inference(superposition,[],[f108,f50])).

fof(f108,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f106])).

% (28155)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f118,plain,
    ( spl11_10
    | spl11_12 ),
    inference(avatar_split_clause,[],[f24,f115,f106])).

fof(f24,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f104,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl11_9 ),
    inference(unit_resulting_resolution,[],[f37,f99])).

fof(f99,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl11_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl11_9
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f100,plain,
    ( spl11_8
    | ~ spl11_9
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f81,f75,f97,f93])).

fof(f81,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3)
    | ~ spl11_5 ),
    inference(resolution,[],[f77,f30])).

% (28153)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f86,plain,
    ( spl11_6
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f79,f75,f83])).

fof(f79,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl11_5 ),
    inference(resolution,[],[f77,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (28133)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (28148)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (28137)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (28149)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (28137)Refutation not found, incomplete strategy% (28137)------------------------------
% 0.20/0.53  % (28137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28137)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28137)Memory used [KB]: 10746
% 0.20/0.53  % (28137)Time elapsed: 0.124 s
% 0.20/0.53  % (28137)------------------------------
% 0.20/0.53  % (28137)------------------------------
% 0.20/0.53  % (28132)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (28141)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (28129)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.56  % (28130)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.56  % (28131)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.56  % (28145)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.56  % (28148)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  fof(f593,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(avatar_sat_refutation,[],[f78,f86,f100,f104,f118,f124,f128,f154,f203,f288,f324,f329,f586,f592])).
% 1.53/0.56  fof(f592,plain,(
% 1.53/0.56    ~spl11_13 | ~spl11_8 | ~spl11_28 | ~spl11_44),
% 1.53/0.56    inference(avatar_split_clause,[],[f588,f584,f279,f93,f121])).
% 1.53/0.56  fof(f121,plain,(
% 1.53/0.56    spl11_13 <=> r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.53/0.56  fof(f93,plain,(
% 1.53/0.56    spl11_8 <=> v1_relat_1(sK3)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.53/0.56  fof(f279,plain,(
% 1.53/0.56    spl11_28 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 1.53/0.56  fof(f584,plain,(
% 1.53/0.56    spl11_44 <=> ! [X0] : (~r2_hidden(sK10(sK4,sK1,sK3),X0) | ~r1_tarski(X0,sK2))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).
% 1.53/0.56  fof(f588,plain,(
% 1.53/0.56    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~spl11_44),
% 1.53/0.56    inference(resolution,[],[f585,f44])).
% 1.53/0.56  fof(f44,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f18])).
% 1.53/0.56  fof(f18,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.53/0.56    inference(ennf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.53/0.56  fof(f585,plain,(
% 1.53/0.56    ( ! [X0] : (~r2_hidden(sK10(sK4,sK1,sK3),X0) | ~r1_tarski(X0,sK2)) ) | ~spl11_44),
% 1.53/0.56    inference(avatar_component_clause,[],[f584])).
% 1.53/0.56  fof(f586,plain,(
% 1.53/0.56    ~spl11_8 | spl11_44 | ~spl11_13 | ~spl11_21),
% 1.53/0.56    inference(avatar_split_clause,[],[f576,f201,f121,f584,f93])).
% 1.53/0.56  fof(f201,plain,(
% 1.53/0.56    spl11_21 <=> ! [X1] : (~r2_hidden(sK10(sK4,X1,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~m1_subset_1(sK10(sK4,X1,sK3),sK2))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.53/0.56  fof(f576,plain,(
% 1.53/0.56    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK10(sK4,sK1,sK3),X0) | ~r1_tarski(X0,sK2) | ~v1_relat_1(sK3)) ) | ~spl11_21),
% 1.53/0.56    inference(duplicate_literal_removal,[],[f574])).
% 1.53/0.56  fof(f574,plain,(
% 1.53/0.56    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK10(sK4,sK1,sK3),X0) | ~r1_tarski(X0,sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1))) ) | ~spl11_21),
% 1.53/0.56    inference(resolution,[],[f365,f46])).
% 1.53/0.56  fof(f46,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f18])).
% 1.53/0.56  fof(f365,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~r2_hidden(sK10(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK10(sK4,X0,sK3),X1) | ~r1_tarski(X1,sK2)) ) | ~spl11_21),
% 1.53/0.56    inference(resolution,[],[f224,f41])).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f17])).
% 1.53/0.56  fof(f17,plain,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.57  fof(f224,plain,(
% 1.53/0.57    ( ! [X0] : (~r2_hidden(sK10(sK4,X0,sK3),sK2) | ~r2_hidden(sK10(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | ~spl11_21),
% 1.53/0.57    inference(resolution,[],[f202,f40])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.53/0.57  fof(f202,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(sK10(sK4,X1,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~r2_hidden(sK10(sK4,X1,sK3),sK1)) ) | ~spl11_21),
% 1.53/0.57    inference(avatar_component_clause,[],[f201])).
% 1.53/0.57  fof(f329,plain,(
% 1.53/0.57    ~spl11_8 | ~spl11_12 | spl11_13 | ~spl11_16),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f325])).
% 1.53/0.57  fof(f325,plain,(
% 1.53/0.57    $false | (~spl11_8 | ~spl11_12 | spl11_13 | ~spl11_16)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f95,f117,f153,f122,f51])).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ( ! [X4,X0,X3,X1] : (r2_hidden(X3,k9_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(equality_resolution,[],[f36])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.53/0.57    inference(cnf_transformation,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 1.53/0.57  fof(f122,plain,(
% 1.53/0.57    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | spl11_13),
% 1.53/0.57    inference(avatar_component_clause,[],[f121])).
% 1.53/0.57  fof(f153,plain,(
% 1.53/0.57    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl11_16),
% 1.53/0.57    inference(avatar_component_clause,[],[f151])).
% 1.53/0.57  fof(f151,plain,(
% 1.53/0.57    spl11_16 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 1.53/0.57  fof(f117,plain,(
% 1.53/0.57    r2_hidden(sK5,sK1) | ~spl11_12),
% 1.53/0.57    inference(avatar_component_clause,[],[f115])).
% 1.53/0.57  fof(f115,plain,(
% 1.53/0.57    spl11_12 <=> r2_hidden(sK5,sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.53/0.57  fof(f95,plain,(
% 1.53/0.57    v1_relat_1(sK3) | ~spl11_8),
% 1.53/0.57    inference(avatar_component_clause,[],[f93])).
% 1.53/0.57  fof(f324,plain,(
% 1.53/0.57    ~spl11_5 | ~spl11_13 | spl11_10),
% 1.53/0.57    inference(avatar_split_clause,[],[f310,f106,f121,f75])).
% 1.53/0.57  fof(f75,plain,(
% 1.53/0.57    spl11_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.53/0.57  fof(f106,plain,(
% 1.53/0.57    spl11_10 <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.53/0.57  fof(f310,plain,(
% 1.53/0.57    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | spl11_10),
% 1.53/0.57    inference(superposition,[],[f107,f50])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f20])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.53/0.57  fof(f107,plain,(
% 1.53/0.57    ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | spl11_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f106])).
% 1.53/0.57  fof(f288,plain,(
% 1.53/0.57    ~spl11_6 | ~spl11_8 | spl11_28),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f286])).
% 1.53/0.57  fof(f286,plain,(
% 1.53/0.57    $false | (~spl11_6 | ~spl11_8 | spl11_28)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f95,f85,f281,f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.53/0.57  fof(f281,plain,(
% 1.53/0.57    ~r1_tarski(k1_relat_1(sK3),sK2) | spl11_28),
% 1.53/0.57    inference(avatar_component_clause,[],[f279])).
% 1.53/0.57  fof(f85,plain,(
% 1.53/0.57    v4_relat_1(sK3,sK2) | ~spl11_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f83])).
% 1.53/0.57  fof(f83,plain,(
% 1.53/0.57    spl11_6 <=> v4_relat_1(sK3,sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.53/0.57  fof(f203,plain,(
% 1.53/0.57    ~spl11_8 | spl11_21 | ~spl11_14),
% 1.53/0.57    inference(avatar_split_clause,[],[f157,f126,f201,f93])).
% 1.53/0.57  fof(f126,plain,(
% 1.53/0.57    spl11_14 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.53/0.57  fof(f157,plain,(
% 1.53/0.57    ( ! [X1] : (~r2_hidden(sK10(sK4,X1,sK3),sK1) | ~m1_subset_1(sK10(sK4,X1,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,X1))) ) | ~spl11_14),
% 1.53/0.57    inference(resolution,[],[f127,f45])).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f127,plain,(
% 1.53/0.57    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl11_14),
% 1.53/0.57    inference(avatar_component_clause,[],[f126])).
% 1.53/0.57  fof(f154,plain,(
% 1.53/0.57    spl11_10 | spl11_16),
% 1.53/0.57    inference(avatar_split_clause,[],[f23,f151,f106])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,negated_conjecture,(
% 1.53/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.53/0.57    inference(negated_conjecture,[],[f10])).
% 1.53/0.57  fof(f10,conjecture,(
% 1.53/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 1.53/0.57  fof(f128,plain,(
% 1.53/0.57    ~spl11_10 | spl11_14),
% 1.53/0.57    inference(avatar_split_clause,[],[f21,f126,f106])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f124,plain,(
% 1.53/0.57    ~spl11_5 | spl11_13 | ~spl11_10),
% 1.53/0.57    inference(avatar_split_clause,[],[f119,f106,f121,f75])).
% 1.53/0.57  fof(f119,plain,(
% 1.53/0.57    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl11_10),
% 1.53/0.57    inference(superposition,[],[f108,f50])).
% 1.53/0.57  fof(f108,plain,(
% 1.53/0.57    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~spl11_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f106])).
% 1.53/0.57  % (28155)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.57  fof(f118,plain,(
% 1.53/0.57    spl11_10 | spl11_12),
% 1.53/0.57    inference(avatar_split_clause,[],[f24,f115,f106])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    spl11_9),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f101])).
% 1.53/0.57  fof(f101,plain,(
% 1.53/0.57    $false | spl11_9),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f37,f99])).
% 1.53/0.57  fof(f99,plain,(
% 1.53/0.57    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl11_9),
% 1.53/0.57    inference(avatar_component_clause,[],[f97])).
% 1.53/0.57  fof(f97,plain,(
% 1.53/0.57    spl11_9 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.53/0.57  fof(f100,plain,(
% 1.53/0.57    spl11_8 | ~spl11_9 | ~spl11_5),
% 1.53/0.57    inference(avatar_split_clause,[],[f81,f75,f97,f93])).
% 1.53/0.57  fof(f81,plain,(
% 1.53/0.57    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK3) | ~spl11_5),
% 1.53/0.57    inference(resolution,[],[f77,f30])).
% 1.53/0.57  % (28153)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.53/0.57  fof(f77,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl11_5),
% 1.53/0.57    inference(avatar_component_clause,[],[f75])).
% 1.53/0.57  fof(f86,plain,(
% 1.53/0.57    spl11_6 | ~spl11_5),
% 1.53/0.57    inference(avatar_split_clause,[],[f79,f75,f83])).
% 1.53/0.57  fof(f79,plain,(
% 1.53/0.57    v4_relat_1(sK3,sK2) | ~spl11_5),
% 1.53/0.57    inference(resolution,[],[f77,f48])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.53/0.57  fof(f78,plain,(
% 1.53/0.57    spl11_5),
% 1.53/0.57    inference(avatar_split_clause,[],[f26,f75])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (28148)------------------------------
% 1.53/0.57  % (28148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (28148)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (28148)Memory used [KB]: 11129
% 1.53/0.57  % (28148)Time elapsed: 0.068 s
% 1.53/0.57  % (28148)------------------------------
% 1.53/0.57  % (28148)------------------------------
% 1.53/0.57  % (28147)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.53/0.57  % (28136)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.64/0.57  % (28125)Success in time 0.217 s
%------------------------------------------------------------------------------
