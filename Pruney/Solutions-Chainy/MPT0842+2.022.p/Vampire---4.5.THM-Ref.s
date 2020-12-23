%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 173 expanded)
%              Number of leaves         :   21 (  74 expanded)
%              Depth                    :    7
%              Number of atoms          :  261 ( 507 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f55,f67,f72,f80,f84,f92,f100,f134,f153,f187,f189,f205,f379,f408,f419])).

fof(f419,plain,
    ( spl9_18
    | ~ spl9_39 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl9_18
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f416,f152])).

fof(f152,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_18
  <=> m1_subset_1(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f416,plain,
    ( m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_39 ),
    inference(resolution,[],[f407,f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f407,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl9_39
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f408,plain,
    ( spl9_39
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f399,f377,f406])).

fof(f377,plain,
    ( spl9_37
  <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f399,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_37 ),
    inference(resolution,[],[f378,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

% (19985)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f378,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),k2_zfmisc_1(sK0,sK2))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f377])).

fof(f379,plain,
    ( spl9_37
    | ~ spl9_2
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f250,f132,f45,f377])).

fof(f45,plain,
    ( spl9_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f132,plain,
    ( spl9_15
  <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f250,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),k2_zfmisc_1(sK0,sK2))
    | ~ spl9_2
    | ~ spl9_15 ),
    inference(resolution,[],[f133,f50])).

fof(f50,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK2)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f133,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f205,plain,
    ( spl9_7
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f193,f78,f53,f70])).

fof(f70,plain,
    ( spl9_7
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f53,plain,
    ( spl9_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f78,plain,
    ( spl9_8
  <=> sP7(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f193,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f192,f54])).

fof(f54,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f192,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_8 ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f79,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f189,plain,
    ( spl9_8
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f188,f82,f65,f78])).

fof(f65,plain,
    ( spl9_6
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f82,plain,
    ( spl9_9
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f188,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(resolution,[],[f182,f66])).

fof(f66,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP7(sK4,X0,sK3) )
    | ~ spl9_9 ),
    inference(resolution,[],[f83,f26])).

fof(f26,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f187,plain,
    ( ~ spl9_7
    | ~ spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f177,f57,f45,f70])).

fof(f57,plain,
    ( spl9_4
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f177,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_2
    | spl9_4 ),
    inference(forward_demodulation,[],[f88,f48])).

fof(f48,plain,
    ( ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl9_2 ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f88,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f153,plain,
    ( ~ spl9_18
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f145,f132,f98,f90,f151])).

fof(f90,plain,
    ( spl9_10
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f98,plain,
    ( spl9_12
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f145,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f139,f99])).

fof(f99,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f139,plain,
    ( ~ r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(resolution,[],[f133,f91])).

fof(f91,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f134,plain,
    ( spl9_15
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f112,f78,f132])).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f79,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(k4_tarski(X3,sK8(X0,X1,X3)),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f100,plain,
    ( spl9_12
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f86,f78,f98])).

fof(f86,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ spl9_8 ),
    inference(resolution,[],[f79,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(sK8(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,
    ( ~ spl9_4
    | spl9_10 ),
    inference(avatar_split_clause,[],[f17,f90,f57])).

fof(f17,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
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
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
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
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f84,plain,
    ( spl9_4
    | spl9_9 ),
    inference(avatar_split_clause,[],[f19,f82,f57])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,
    ( spl9_8
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f76,f70,f53,f78])).

fof(f76,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f73,f54])).

fof(f73,plain,
    ( sP7(sK4,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP7(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,
    ( spl9_7
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f68,f57,f45,f70])).

fof(f68,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f58,f48])).

fof(f58,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f67,plain,
    ( spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f20,f65,f57])).

fof(f20,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f51,f45,f53])).

fof(f51,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f47,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (19996)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (19981)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (19989)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (19983)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (19981)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (19997)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (19992)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f420,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f47,f55,f67,f72,f80,f84,f92,f100,f134,f153,f187,f189,f205,f379,f408,f419])).
% 0.21/0.52  fof(f419,plain,(
% 0.21/0.52    spl9_18 | ~spl9_39),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f418])).
% 0.21/0.52  fof(f418,plain,(
% 0.21/0.52    $false | (spl9_18 | ~spl9_39)),
% 0.21/0.52    inference(subsumption_resolution,[],[f416,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | spl9_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl9_18 <=> m1_subset_1(sK8(sK3,sK1,sK4),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.52  fof(f416,plain,(
% 0.21/0.52    m1_subset_1(sK8(sK3,sK1,sK4),sK2) | ~spl9_39),
% 0.21/0.52    inference(resolution,[],[f407,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.52  fof(f407,plain,(
% 0.21/0.52    r2_hidden(sK8(sK3,sK1,sK4),sK2) | ~spl9_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f406])).
% 0.21/0.52  fof(f406,plain,(
% 0.21/0.52    spl9_39 <=> r2_hidden(sK8(sK3,sK1,sK4),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.21/0.52  fof(f408,plain,(
% 0.21/0.52    spl9_39 | ~spl9_37),
% 0.21/0.52    inference(avatar_split_clause,[],[f399,f377,f406])).
% 0.21/0.52  fof(f377,plain,(
% 0.21/0.52    spl9_37 <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),k2_zfmisc_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    r2_hidden(sK8(sK3,sK1,sK4),sK2) | ~spl9_37),
% 0.21/0.52    inference(resolution,[],[f378,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  % (19985)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),k2_zfmisc_1(sK0,sK2)) | ~spl9_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f377])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    spl9_37 | ~spl9_2 | ~spl9_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f250,f132,f45,f377])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl9_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl9_15 <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),k2_zfmisc_1(sK0,sK2)) | (~spl9_2 | ~spl9_15)),
% 0.21/0.52    inference(resolution,[],[f133,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,k2_zfmisc_1(sK0,sK2))) ) | ~spl9_2),
% 0.21/0.52    inference(resolution,[],[f46,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl9_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f45])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3) | ~spl9_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    spl9_7 | ~spl9_3 | ~spl9_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f193,f78,f53,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl9_7 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl9_3 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl9_8 <=> sP7(sK4,sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl9_3 | ~spl9_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl9_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f53])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl9_8),
% 0.21/0.52    inference(resolution,[],[f79,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    sP7(sK4,sK1,sK3) | ~spl9_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl9_8 | ~spl9_6 | ~spl9_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f188,f82,f65,f78])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl9_6 <=> r2_hidden(sK5,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl9_9 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    sP7(sK4,sK1,sK3) | (~spl9_6 | ~spl9_9)),
% 0.21/0.52    inference(resolution,[],[f182,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    r2_hidden(sK5,sK1) | ~spl9_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK5,X0) | sP7(sK4,X0,sK3)) ) | ~spl9_9),
% 0.21/0.52    inference(resolution,[],[f83,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP7(X3,X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl9_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ~spl9_7 | ~spl9_2 | spl9_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f177,f57,f45,f70])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl9_4 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl9_2 | spl9_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f88,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl9_2),
% 0.21/0.52    inference(resolution,[],[f46,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl9_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~spl9_18 | ~spl9_10 | ~spl9_12 | ~spl9_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f145,f132,f98,f90,f151])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl9_10 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl9_12 <=> r2_hidden(sK8(sK3,sK1,sK4),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | (~spl9_10 | ~spl9_12 | ~spl9_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f139,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    r2_hidden(sK8(sK3,sK1,sK4),sK1) | ~spl9_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f98])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~r2_hidden(sK8(sK3,sK1,sK4),sK1) | ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | (~spl9_10 | ~spl9_15)),
% 0.21/0.52    inference(resolution,[],[f133,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl9_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl9_15 | ~spl9_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f78,f132])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3) | ~spl9_8),
% 0.21/0.52    inference(resolution,[],[f79,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(k4_tarski(X3,sK8(X0,X1,X3)),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl9_12 | ~spl9_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f86,f78,f98])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    r2_hidden(sK8(sK3,sK1,sK4),sK1) | ~spl9_8),
% 0.21/0.52    inference(resolution,[],[f79,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(sK8(X0,X1,X3),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~spl9_4 | spl9_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f90,f57])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl9_4 | spl9_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f82,f57])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl9_8 | ~spl9_3 | ~spl9_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f76,f70,f53,f78])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    sP7(sK4,sK1,sK3) | (~spl9_3 | ~spl9_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f54])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    sP7(sK4,sK1,sK3) | ~v1_relat_1(sK3) | ~spl9_7),
% 0.21/0.52    inference(resolution,[],[f71,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP7(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl9_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl9_7 | ~spl9_2 | ~spl9_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f57,f45,f70])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl9_2 | ~spl9_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f58,f48])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl9_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl9_4 | spl9_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f65,f57])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl9_3 | ~spl9_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f45,f53])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl9_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3) | ~spl9_2),
% 0.21/0.52    inference(resolution,[],[f46,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl9_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f45])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (19981)------------------------------
% 0.21/0.52  % (19981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19981)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (19981)Memory used [KB]: 6396
% 0.21/0.52  % (19981)Time elapsed: 0.078 s
% 0.21/0.52  % (19981)------------------------------
% 0.21/0.52  % (19981)------------------------------
% 0.21/0.53  % (19980)Success in time 0.166 s
%------------------------------------------------------------------------------
