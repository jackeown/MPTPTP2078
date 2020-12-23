%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 145 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  221 ( 594 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f69,f108,f186])).

fof(f186,plain,
    ( ~ spl10_1
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f184,f81])).

fof(f81,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f78,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
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

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
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

fof(f184,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f183,f111])).

fof(f111,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f110,f22])).

fof(f110,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_1 ),
    inference(superposition,[],[f50,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f50,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl10_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f183,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_5 ),
    inference(resolution,[],[f181,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f181,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X1)) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f180,f121])).

fof(f121,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2,X3,sK3),sK2)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f120,f81])).

% (32650)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f120,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2,X3,sK3),sK2)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
      | r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f77,f43])).

fof(f43,plain,(
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

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f180,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X1))
        | ~ r2_hidden(sK9(sK4,X1,sK3),sK2) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f179,f23])).

fof(f23,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X1))
        | ~ r2_hidden(sK9(sK4,X1,sK3),sK2)
        | v1_xboole_0(sK2) )
    | ~ spl10_5 ),
    inference(resolution,[],[f148,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f144,f81])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f68,f38])).

fof(f68,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_5
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f108,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f105,f54])).

fof(f54,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f105,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl10_1
    | ~ spl10_3 ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f98,f81])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3) )
    | spl10_1 ),
    inference(resolution,[],[f97,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f96,f22])).

fof(f96,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl10_1 ),
    inference(superposition,[],[f49,f41])).

fof(f49,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f69,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f17,f67,f48])).

fof(f17,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f19,f57,f48])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f20,f52,f48])).

fof(f20,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (32648)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (32644)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (32653)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (32641)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (32649)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (32640)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (32657)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (32638)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (32642)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (32658)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (32655)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (32639)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (32654)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (32639)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 1.26/0.51  % (32651)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.26/0.51  % (32647)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.26/0.51  % (32646)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.26/0.52  % (32643)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f187,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(avatar_sat_refutation,[],[f55,f60,f69,f108,f186])).
% 1.26/0.52  fof(f186,plain,(
% 1.26/0.52    ~spl10_1 | ~spl10_5),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f185])).
% 1.26/0.52  fof(f185,plain,(
% 1.26/0.52    $false | (~spl10_1 | ~spl10_5)),
% 1.26/0.52    inference(subsumption_resolution,[],[f184,f81])).
% 1.26/0.52  fof(f81,plain,(
% 1.26/0.52    v1_relat_1(sK3)),
% 1.26/0.52    inference(subsumption_resolution,[],[f78,f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.26/0.52  fof(f78,plain,(
% 1.26/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 1.26/0.52    inference(resolution,[],[f22,f26])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f12])).
% 1.26/0.52  fof(f12,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.26/0.52    inference(cnf_transformation,[],[f11])).
% 1.26/0.52  fof(f11,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,negated_conjecture,(
% 1.26/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.26/0.52    inference(negated_conjecture,[],[f9])).
% 1.26/0.52  fof(f9,conjecture,(
% 1.26/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).
% 1.26/0.52  fof(f184,plain,(
% 1.26/0.52    ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_5)),
% 1.26/0.52    inference(subsumption_resolution,[],[f183,f111])).
% 1.26/0.52  fof(f111,plain,(
% 1.26/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_1),
% 1.26/0.52    inference(subsumption_resolution,[],[f110,f22])).
% 1.26/0.52  fof(f110,plain,(
% 1.26/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_1),
% 1.26/0.52    inference(superposition,[],[f50,f41])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f16])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.26/0.52  fof(f50,plain,(
% 1.26/0.52    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_1),
% 1.26/0.52    inference(avatar_component_clause,[],[f48])).
% 1.26/0.52  fof(f48,plain,(
% 1.26/0.52    spl10_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.26/0.52  fof(f183,plain,(
% 1.26/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~spl10_5),
% 1.26/0.52    inference(duplicate_literal_removal,[],[f182])).
% 1.26/0.52  fof(f182,plain,(
% 1.26/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_5),
% 1.26/0.52    inference(resolution,[],[f181,f39])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f15,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.26/0.52    inference(ennf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.26/0.52  fof(f181,plain,(
% 1.26/0.52    ( ! [X1] : (~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X1))) ) | ~spl10_5),
% 1.26/0.52    inference(subsumption_resolution,[],[f180,f121])).
% 1.26/0.52  fof(f121,plain,(
% 1.26/0.52    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),sK2) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f120,f81])).
% 1.26/0.52  % (32650)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.52  fof(f120,plain,(
% 1.26/0.52    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 1.26/0.52    inference(resolution,[],[f102,f38])).
% 1.26/0.52  fof(f38,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f102,plain,(
% 1.26/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X3,sK2)) )),
% 1.26/0.52    inference(resolution,[],[f77,f43])).
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.26/0.52  fof(f77,plain,(
% 1.26/0.52    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,sK3)) )),
% 1.26/0.52    inference(resolution,[],[f22,f32])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f14])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.26/0.52  fof(f180,plain,(
% 1.26/0.52    ( ! [X1] : (~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X1)) | ~r2_hidden(sK9(sK4,X1,sK3),sK2)) ) | ~spl10_5),
% 1.26/0.52    inference(subsumption_resolution,[],[f179,f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ~v1_xboole_0(sK2)),
% 1.26/0.52    inference(cnf_transformation,[],[f11])).
% 1.26/0.52  fof(f179,plain,(
% 1.26/0.52    ( ! [X1] : (~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X1)) | ~r2_hidden(sK9(sK4,X1,sK3),sK2) | v1_xboole_0(sK2)) ) | ~spl10_5),
% 1.26/0.52    inference(resolution,[],[f148,f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f13])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.26/0.52  fof(f148,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 1.26/0.52    inference(subsumption_resolution,[],[f144,f81])).
% 1.26/0.52  fof(f144,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 1.26/0.52    inference(resolution,[],[f68,f38])).
% 1.26/0.52  fof(f68,plain,(
% 1.26/0.52    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_5),
% 1.26/0.52    inference(avatar_component_clause,[],[f67])).
% 1.26/0.52  fof(f67,plain,(
% 1.26/0.52    spl10_5 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.26/0.52  fof(f108,plain,(
% 1.26/0.52    spl10_1 | ~spl10_2 | ~spl10_3),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f107])).
% 1.26/0.52  fof(f107,plain,(
% 1.26/0.52    $false | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.26/0.52    inference(subsumption_resolution,[],[f105,f54])).
% 1.26/0.52  fof(f54,plain,(
% 1.26/0.52    r2_hidden(sK5,sK1) | ~spl10_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f52])).
% 1.26/0.52  fof(f52,plain,(
% 1.26/0.52    spl10_2 <=> r2_hidden(sK5,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.26/0.52  fof(f105,plain,(
% 1.26/0.52    ~r2_hidden(sK5,sK1) | (spl10_1 | ~spl10_3)),
% 1.26/0.52    inference(resolution,[],[f100,f59])).
% 1.26/0.52  fof(f59,plain,(
% 1.26/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_3),
% 1.26/0.52    inference(avatar_component_clause,[],[f57])).
% 1.26/0.52  fof(f57,plain,(
% 1.26/0.52    spl10_3 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.26/0.52  fof(f100,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_1),
% 1.26/0.52    inference(subsumption_resolution,[],[f99,f46])).
% 1.26/0.52  fof(f46,plain,(
% 1.26/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.26/0.52    inference(equality_resolution,[],[f33])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.26/0.52    inference(cnf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.26/0.52  fof(f99,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_1),
% 1.26/0.52    inference(subsumption_resolution,[],[f98,f81])).
% 1.26/0.52  fof(f98,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~v1_relat_1(sK3)) ) | spl10_1),
% 1.26/0.52    inference(resolution,[],[f97,f40])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f97,plain,(
% 1.26/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl10_1),
% 1.26/0.52    inference(subsumption_resolution,[],[f96,f22])).
% 1.26/0.52  fof(f96,plain,(
% 1.26/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl10_1),
% 1.26/0.52    inference(superposition,[],[f49,f41])).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_1),
% 1.26/0.52    inference(avatar_component_clause,[],[f48])).
% 1.26/0.52  fof(f69,plain,(
% 1.26/0.52    ~spl10_1 | spl10_5),
% 1.26/0.52    inference(avatar_split_clause,[],[f17,f67,f48])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f11])).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    spl10_1 | spl10_3),
% 1.26/0.52    inference(avatar_split_clause,[],[f19,f57,f48])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.26/0.52    inference(cnf_transformation,[],[f11])).
% 1.26/0.52  fof(f55,plain,(
% 1.26/0.52    spl10_1 | spl10_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f20,f52,f48])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.26/0.52    inference(cnf_transformation,[],[f11])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (32639)------------------------------
% 1.26/0.52  % (32639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (32639)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (32639)Memory used [KB]: 10746
% 1.26/0.52  % (32639)Time elapsed: 0.079 s
% 1.26/0.52  % (32639)------------------------------
% 1.26/0.52  % (32639)------------------------------
% 1.26/0.52  % (32656)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.26/0.52  % (32645)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.40/0.53  % (32652)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.40/0.53  % (32637)Success in time 0.173 s
%------------------------------------------------------------------------------
