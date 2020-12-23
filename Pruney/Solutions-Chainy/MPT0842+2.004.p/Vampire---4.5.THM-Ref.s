%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 160 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  269 ( 563 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f62,f85,f90,f123,f127,f134,f143,f151,f225,f260,f264])).

fof(f264,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f259,f72])).

fof(f72,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

% (25961)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f259,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl7_25
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f260,plain,
    ( ~ spl7_25
    | ~ spl7_7
    | spl7_21 ),
    inference(avatar_split_clause,[],[f255,f223,f81,f258])).

fof(f81,plain,
    ( spl7_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f223,plain,
    ( spl7_21
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f255,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK2)
    | spl7_21 ),
    inference(resolution,[],[f238,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f238,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl7_21 ),
    inference(resolution,[],[f224,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f224,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( ~ spl7_13
    | ~ spl7_7
    | ~ spl7_21
    | spl7_12 ),
    inference(avatar_split_clause,[],[f215,f138,f223,f81,f141])).

fof(f141,plain,
    ( spl7_13
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f138,plain,
    ( spl7_12
  <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f215,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl7_12 ),
    inference(resolution,[],[f154,f35])).

% (25953)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK4,sK1,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) )
    | spl7_12 ),
    inference(resolution,[],[f139,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f139,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f151,plain,
    ( ~ spl7_1
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl7_1
    | spl7_13 ),
    inference(resolution,[],[f142,f132])).

fof(f132,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f45,f99])).

fof(f99,plain,(
    ! [X9] : k8_relset_1(sK0,sK2,sK3,X9) = k10_relat_1(sK3,X9) ),
    inference(resolution,[],[f42,f28])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f45,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl7_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f142,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( ~ spl7_7
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f136,f118,f141,f138,f81])).

fof(f118,plain,
    ( spl7_10
  <=> ! [X0] :
        ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
        | ~ m1_subset_1(sK6(sK4,X0,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f136,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f119,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
        | ~ m1_subset_1(sK6(sK4,X0,sK3),sK2) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f134,plain,
    ( ~ spl7_7
    | spl7_10
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f133,f60,f118,f81])).

fof(f60,plain,
    ( spl7_5
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
        | ~ m1_subset_1(sK6(sK4,X0,sK3),sK2)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl7_5 ),
    inference(resolution,[],[f61,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f127,plain,
    ( ~ spl7_8
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f124,f108,f51,f47,f88])).

fof(f88,plain,
    ( spl7_8
  <=> r2_hidden(sK5,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f47,plain,
    ( spl7_2
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f51,plain,
    ( spl7_3
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f108,plain,
    ( spl7_9
  <=> ! [X10] :
        ( ~ r2_hidden(X10,k2_relat_1(sK3))
        | ~ r2_hidden(X10,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X10),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f124,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ r2_hidden(sK5,k2_relat_1(sK3))
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f109,f52])).

fof(f52,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f109,plain,
    ( ! [X10] :
        ( ~ r2_hidden(k4_tarski(sK4,X10),sK3)
        | ~ r2_hidden(X10,sK1)
        | ~ r2_hidden(X10,k2_relat_1(sK3)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f123,plain,
    ( ~ spl7_7
    | spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f122,f44,f108,f81])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3) )
    | spl7_1 ),
    inference(resolution,[],[f121,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl7_1 ),
    inference(forward_demodulation,[],[f58,f99])).

fof(f58,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f44])).

% (25944)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f90,plain,
    ( spl7_8
    | ~ spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f86,f51,f81,f88])).

fof(f86,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK5,k2_relat_1(sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f34,f52])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f85,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl7_7 ),
    inference(resolution,[],[f82,f66])).

fof(f66,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

% (25952)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (25952)Refutation not found, incomplete strategy% (25952)------------------------------
% (25952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25952)Termination reason: Refutation not found, incomplete strategy

% (25952)Memory used [KB]: 10618
% (25952)Time elapsed: 0.099 s
% (25952)------------------------------
% (25952)------------------------------
% (25956)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f82,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f62,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f23,f60,f44])).

fof(f23,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f25,f51,f44])).

fof(f25,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f26,f47,f44])).

fof(f26,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (25964)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (25947)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (25946)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (25954)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (25960)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (25965)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (25954)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f49,f53,f62,f85,f90,f123,f127,f134,f143,f151,f225,f260,f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    spl7_25),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    $false | spl7_25),
% 0.21/0.51    inference(resolution,[],[f259,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    v5_relat_1(sK3,sK2)),
% 0.21/0.51    inference(resolution,[],[f40,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.51  % (25961)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ~v5_relat_1(sK3,sK2) | spl7_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f258])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl7_25 <=> v5_relat_1(sK3,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ~spl7_25 | ~spl7_7 | spl7_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f255,f223,f81,f258])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl7_7 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl7_21 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK2) | spl7_21),
% 0.21/0.51    inference(resolution,[],[f238,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK3),sK2) | spl7_21),
% 0.21/0.51    inference(resolution,[],[f224,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f223])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ~spl7_13 | ~spl7_7 | ~spl7_21 | spl7_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f215,f138,f223,f81,f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl7_13 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl7_12 <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl7_12),
% 0.21/0.51    inference(resolution,[],[f154,f35])).
% 0.21/0.51  % (25953)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK6(sK4,sK1,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2))) ) | spl7_12),
% 0.21/0.51    inference(resolution,[],[f139,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | spl7_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~spl7_1 | spl7_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    $false | (~spl7_1 | spl7_13)),
% 0.21/0.51    inference(resolution,[],[f142,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl7_1),
% 0.21/0.51    inference(forward_demodulation,[],[f45,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X9] : (k8_relset_1(sK0,sK2,sK3,X9) = k10_relat_1(sK3,X9)) )),
% 0.21/0.51    inference(resolution,[],[f42,f28])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl7_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl7_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~spl7_7 | ~spl7_12 | ~spl7_13 | ~spl7_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f118,f141,f138,f81])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl7_10 <=> ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~m1_subset_1(sK6(sK4,X0,sK3),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | ~v1_relat_1(sK3) | ~spl7_10),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl7_10),
% 0.21/0.51    inference(resolution,[],[f119,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~m1_subset_1(sK6(sK4,X0,sK3),sK2)) ) | ~spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~spl7_7 | spl7_10 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f60,f118,f81])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl7_5 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~m1_subset_1(sK6(sK4,X0,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl7_5),
% 0.21/0.51    inference(resolution,[],[f61,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~spl7_8 | ~spl7_2 | ~spl7_3 | ~spl7_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f124,f108,f51,f47,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl7_8 <=> r2_hidden(sK5,k2_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl7_2 <=> r2_hidden(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl7_3 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl7_9 <=> ! [X10] : (~r2_hidden(X10,k2_relat_1(sK3)) | ~r2_hidden(X10,sK1) | ~r2_hidden(k4_tarski(sK4,X10),sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~r2_hidden(sK5,sK1) | ~r2_hidden(sK5,k2_relat_1(sK3)) | (~spl7_3 | ~spl7_9)),
% 0.21/0.51    inference(resolution,[],[f109,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X10] : (~r2_hidden(k4_tarski(sK4,X10),sK3) | ~r2_hidden(X10,sK1) | ~r2_hidden(X10,k2_relat_1(sK3))) ) | ~spl7_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~spl7_7 | spl7_9 | spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f122,f44,f108,f81])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~v1_relat_1(sK3)) ) | spl7_1),
% 0.21/0.51    inference(resolution,[],[f121,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl7_1),
% 0.21/0.51    inference(forward_demodulation,[],[f58,f99])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  % (25944)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl7_8 | ~spl7_7 | ~spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f86,f51,f81,f88])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | r2_hidden(sK5,k2_relat_1(sK3)) | ~spl7_3),
% 0.21/0.51    inference(resolution,[],[f34,f52])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl7_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    $false | spl7_7),
% 0.21/0.51    inference(resolution,[],[f82,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f39,f28])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % (25952)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (25952)Refutation not found, incomplete strategy% (25952)------------------------------
% 0.21/0.52  % (25952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25952)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25952)Memory used [KB]: 10618
% 0.21/0.52  % (25952)Time elapsed: 0.099 s
% 0.21/0.52  % (25952)------------------------------
% 0.21/0.52  % (25952)------------------------------
% 0.21/0.52  % (25956)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.30/0.52  fof(f18,plain,(
% 1.30/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.52    inference(ennf_transformation,[],[f6])).
% 1.30/0.52  fof(f6,axiom,(
% 1.30/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.30/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.30/0.52  fof(f82,plain,(
% 1.30/0.52    ~v1_relat_1(sK3) | spl7_7),
% 1.30/0.52    inference(avatar_component_clause,[],[f81])).
% 1.30/0.52  fof(f62,plain,(
% 1.30/0.52    ~spl7_1 | spl7_5),
% 1.30/0.52    inference(avatar_split_clause,[],[f23,f60,f44])).
% 1.30/0.52  fof(f23,plain,(
% 1.30/0.52    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 1.30/0.52    inference(cnf_transformation,[],[f13])).
% 1.30/0.52  fof(f53,plain,(
% 1.30/0.52    spl7_1 | spl7_3),
% 1.30/0.52    inference(avatar_split_clause,[],[f25,f51,f44])).
% 1.30/0.52  fof(f25,plain,(
% 1.30/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.30/0.52    inference(cnf_transformation,[],[f13])).
% 1.30/0.52  fof(f49,plain,(
% 1.30/0.52    spl7_1 | spl7_2),
% 1.30/0.52    inference(avatar_split_clause,[],[f26,f47,f44])).
% 1.30/0.52  fof(f26,plain,(
% 1.30/0.52    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.30/0.52    inference(cnf_transformation,[],[f13])).
% 1.30/0.52  % SZS output end Proof for theBenchmark
% 1.30/0.52  % (25954)------------------------------
% 1.30/0.52  % (25954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (25954)Termination reason: Refutation
% 1.30/0.52  
% 1.30/0.52  % (25954)Memory used [KB]: 10746
% 1.30/0.52  % (25954)Time elapsed: 0.095 s
% 1.30/0.52  % (25954)------------------------------
% 1.30/0.52  % (25954)------------------------------
% 1.30/0.52  % (25950)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.30/0.52  % (25938)Success in time 0.166 s
%------------------------------------------------------------------------------
