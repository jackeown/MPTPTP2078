%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:55 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 204 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  229 ( 762 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f134,f153,f259,f293])).

fof(f293,plain,
    ( spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f74,f114,f97,f133,f269,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f269,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f74,f133,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f133,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl9_4
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f97,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_2
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f114,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f74,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f51,f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f259,plain,
    ( ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f208,f215,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f215,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f102,f101,f152])).

fof(f152,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_5
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f74,f98,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f102,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f74,f98,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f208,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f175,f100,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f100,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k1_relat_1(sK3))
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f74,f98,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f175,plain,(
    r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f88,f162])).

fof(f162,plain,(
    sK2 = k1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f121,f157,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f157,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f59,f70])).

fof(f70,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK7(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f63,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f63,plain,(
    r2_hidden(sK7(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f121,plain,(
    k1_xboole_0 != sK2 ),
    inference(superposition,[],[f59,f64])).

fof(f64,plain,(
    sK2 = k2_xboole_0(k1_tarski(sK7(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f61,f60])).

fof(f61,plain,(
    r2_hidden(sK7(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f35,f52])).

fof(f35,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    r1_tarski(k1_relat_1(sK3),k1_relat_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(unit_resulting_resolution,[],[f74,f51,f75,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f75,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f153,plain,
    ( spl9_5
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f76,f96,f151])).

fof(f76,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f29,f73])).

fof(f73,plain,(
    ! [X0] : k7_relset_1(sK2,sK0,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f29,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f134,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f78,f96,f131])).

fof(f78,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(backward_demodulation,[],[f31,f73])).

fof(f31,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f115,plain,
    ( spl9_3
    | spl9_2 ),
    inference(avatar_split_clause,[],[f79,f96,f112])).

fof(f79,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f32,f73])).

fof(f32,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (795541505)
% 0.13/0.37  ipcrm: permission denied for id (793346050)
% 0.13/0.37  ipcrm: permission denied for id (793378819)
% 0.13/0.37  ipcrm: permission denied for id (795574276)
% 0.13/0.37  ipcrm: permission denied for id (795607045)
% 0.13/0.37  ipcrm: permission denied for id (793411590)
% 0.13/0.37  ipcrm: permission denied for id (793444359)
% 0.13/0.38  ipcrm: permission denied for id (793477132)
% 0.13/0.38  ipcrm: permission denied for id (793509902)
% 0.21/0.38  ipcrm: permission denied for id (793542673)
% 0.21/0.39  ipcrm: permission denied for id (793575442)
% 0.21/0.39  ipcrm: permission denied for id (793608211)
% 0.21/0.39  ipcrm: permission denied for id (793706518)
% 0.21/0.39  ipcrm: permission denied for id (795967512)
% 0.21/0.40  ipcrm: permission denied for id (796000281)
% 0.21/0.40  ipcrm: permission denied for id (796033050)
% 0.21/0.40  ipcrm: permission denied for id (796131357)
% 0.21/0.40  ipcrm: permission denied for id (796196895)
% 0.21/0.40  ipcrm: permission denied for id (796229664)
% 0.21/0.41  ipcrm: permission denied for id (796295202)
% 0.21/0.41  ipcrm: permission denied for id (796327971)
% 0.21/0.41  ipcrm: permission denied for id (796393509)
% 0.21/0.41  ipcrm: permission denied for id (794001446)
% 0.21/0.42  ipcrm: permission denied for id (796655661)
% 0.21/0.42  ipcrm: permission denied for id (796721199)
% 0.21/0.43  ipcrm: permission denied for id (794066995)
% 0.21/0.43  ipcrm: permission denied for id (796885044)
% 0.21/0.43  ipcrm: permission denied for id (796917813)
% 0.21/0.43  ipcrm: permission denied for id (796950582)
% 0.21/0.43  ipcrm: permission denied for id (796983351)
% 0.21/0.44  ipcrm: permission denied for id (797081657)
% 0.21/0.44  ipcrm: permission denied for id (797179963)
% 0.21/0.44  ipcrm: permission denied for id (797212732)
% 0.21/0.44  ipcrm: permission denied for id (797311039)
% 0.21/0.45  ipcrm: permission denied for id (794132545)
% 0.21/0.45  ipcrm: permission denied for id (797376578)
% 0.21/0.45  ipcrm: permission denied for id (797409347)
% 0.21/0.45  ipcrm: permission denied for id (794165316)
% 0.21/0.45  ipcrm: permission denied for id (794230854)
% 0.21/0.45  ipcrm: permission denied for id (797474887)
% 0.21/0.46  ipcrm: permission denied for id (794296392)
% 0.21/0.46  ipcrm: permission denied for id (794394697)
% 0.21/0.46  ipcrm: permission denied for id (794361930)
% 0.21/0.46  ipcrm: permission denied for id (794427467)
% 0.21/0.46  ipcrm: permission denied for id (794460236)
% 0.21/0.46  ipcrm: permission denied for id (797507661)
% 0.21/0.46  ipcrm: permission denied for id (797573199)
% 0.21/0.47  ipcrm: permission denied for id (797638737)
% 0.21/0.47  ipcrm: permission denied for id (797704275)
% 0.21/0.47  ipcrm: permission denied for id (794656853)
% 0.21/0.47  ipcrm: permission denied for id (794689622)
% 0.21/0.48  ipcrm: permission denied for id (797802584)
% 0.21/0.48  ipcrm: permission denied for id (794722393)
% 0.21/0.48  ipcrm: permission denied for id (794755162)
% 0.21/0.48  ipcrm: permission denied for id (797868124)
% 0.21/0.48  ipcrm: permission denied for id (797900893)
% 0.21/0.49  ipcrm: permission denied for id (797999200)
% 0.21/0.49  ipcrm: permission denied for id (798097507)
% 0.21/0.49  ipcrm: permission denied for id (798163045)
% 0.21/0.50  ipcrm: permission denied for id (798261352)
% 0.21/0.50  ipcrm: permission denied for id (798294121)
% 0.21/0.50  ipcrm: permission denied for id (795050090)
% 0.21/0.50  ipcrm: permission denied for id (795082860)
% 0.21/0.50  ipcrm: permission denied for id (795115629)
% 0.21/0.50  ipcrm: permission denied for id (795181167)
% 0.21/0.51  ipcrm: permission denied for id (798392432)
% 0.21/0.51  ipcrm: permission denied for id (795246705)
% 0.21/0.51  ipcrm: permission denied for id (798425202)
% 0.21/0.51  ipcrm: permission denied for id (798457971)
% 0.21/0.51  ipcrm: permission denied for id (795312244)
% 0.21/0.51  ipcrm: permission denied for id (798523510)
% 0.21/0.52  ipcrm: permission denied for id (795377784)
% 0.21/0.52  ipcrm: permission denied for id (798589049)
% 0.21/0.52  ipcrm: permission denied for id (798654587)
% 0.21/0.52  ipcrm: permission denied for id (795443324)
% 0.21/0.52  ipcrm: permission denied for id (798687357)
% 0.37/0.52  ipcrm: permission denied for id (795476095)
% 0.38/0.65  % (31193)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.38/0.66  % (31217)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.38/0.66  % (31209)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.38/0.66  % (31200)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.38/0.67  % (31198)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.38/0.67  % (31193)Refutation found. Thanks to Tanya!
% 0.38/0.67  % SZS status Theorem for theBenchmark
% 0.38/0.67  % SZS output start Proof for theBenchmark
% 0.38/0.67  fof(f294,plain,(
% 0.38/0.67    $false),
% 0.38/0.67    inference(avatar_sat_refutation,[],[f115,f134,f153,f259,f293])).
% 0.38/0.67  fof(f293,plain,(
% 0.38/0.67    spl9_2 | ~spl9_3 | ~spl9_4),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f287])).
% 0.38/0.67  fof(f287,plain,(
% 0.38/0.67    $false | (spl9_2 | ~spl9_3 | ~spl9_4)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f74,f114,f97,f133,f269,f41])).
% 0.38/0.67  fof(f41,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f18])).
% 0.38/0.67  fof(f18,plain,(
% 0.38/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.38/0.67    inference(ennf_transformation,[],[f10])).
% 0.38/0.67  fof(f10,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.38/0.67  fof(f269,plain,(
% 0.38/0.67    r2_hidden(sK5,k1_relat_1(sK3)) | ~spl9_4),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f74,f133,f42])).
% 0.38/0.67  fof(f42,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f20])).
% 0.38/0.67  fof(f20,plain,(
% 0.38/0.67    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.38/0.67    inference(flattening,[],[f19])).
% 0.38/0.67  fof(f19,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.38/0.67    inference(ennf_transformation,[],[f12])).
% 0.38/0.67  fof(f12,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.38/0.67  fof(f133,plain,(
% 0.38/0.67    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl9_4),
% 0.38/0.67    inference(avatar_component_clause,[],[f131])).
% 0.38/0.67  fof(f131,plain,(
% 0.38/0.67    spl9_4 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.38/0.67  fof(f97,plain,(
% 0.38/0.67    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | spl9_2),
% 0.38/0.67    inference(avatar_component_clause,[],[f96])).
% 0.38/0.67  fof(f96,plain,(
% 0.38/0.67    spl9_2 <=> r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.38/0.67  fof(f114,plain,(
% 0.38/0.67    r2_hidden(sK5,sK1) | ~spl9_3),
% 0.38/0.67    inference(avatar_component_clause,[],[f112])).
% 0.38/0.67  fof(f112,plain,(
% 0.38/0.67    spl9_3 <=> r2_hidden(sK5,sK1)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.38/0.67  fof(f74,plain,(
% 0.38/0.67    v1_relat_1(sK3)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f51,f34,f48])).
% 0.38/0.67  fof(f48,plain,(
% 0.38/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f23])).
% 0.38/0.67  fof(f23,plain,(
% 0.38/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f8])).
% 0.38/0.67  fof(f8,axiom,(
% 0.38/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.38/0.67  fof(f34,plain,(
% 0.38/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f17,plain,(
% 0.38/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f16])).
% 0.38/0.67  fof(f16,negated_conjecture,(
% 0.38/0.67    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.38/0.67    inference(negated_conjecture,[],[f15])).
% 0.38/0.67  fof(f15,conjecture,(
% 0.38/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.38/0.67  fof(f51,plain,(
% 0.38/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f9])).
% 0.38/0.67  fof(f9,axiom,(
% 0.38/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.38/0.67  fof(f259,plain,(
% 0.38/0.67    ~spl9_2 | ~spl9_5),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f257])).
% 0.38/0.67  fof(f257,plain,(
% 0.38/0.67    $false | (~spl9_2 | ~spl9_5)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f208,f215,f44])).
% 0.38/0.67  fof(f44,plain,(
% 0.38/0.67    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f21])).
% 0.38/0.67  fof(f21,plain,(
% 0.38/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.38/0.67    inference(ennf_transformation,[],[f6])).
% 0.38/0.67  fof(f6,axiom,(
% 0.38/0.67    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.38/0.67  fof(f215,plain,(
% 0.38/0.67    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl9_2 | ~spl9_5)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f102,f101,f152])).
% 0.38/0.67  fof(f152,plain,(
% 0.38/0.67    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl9_5),
% 0.38/0.67    inference(avatar_component_clause,[],[f151])).
% 0.38/0.67  fof(f151,plain,(
% 0.38/0.67    spl9_5 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.38/0.67  fof(f101,plain,(
% 0.38/0.67    r2_hidden(k4_tarski(sK6(sK4,sK1,sK3),sK4),sK3) | ~spl9_2),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f74,f98,f39])).
% 0.38/0.67  fof(f39,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f18])).
% 0.38/0.67  fof(f98,plain,(
% 0.38/0.67    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~spl9_2),
% 0.38/0.67    inference(avatar_component_clause,[],[f96])).
% 0.38/0.67  fof(f102,plain,(
% 0.38/0.67    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~spl9_2),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f74,f98,f40])).
% 0.38/0.67  fof(f40,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f18])).
% 0.38/0.67  fof(f208,plain,(
% 0.38/0.67    r2_hidden(sK6(sK4,sK1,sK3),sK2) | ~spl9_2),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f175,f100,f56])).
% 0.38/0.67  fof(f56,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f27])).
% 0.38/0.67  fof(f27,plain,(
% 0.38/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f2])).
% 0.38/0.67  fof(f2,axiom,(
% 0.38/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.38/0.67  fof(f100,plain,(
% 0.38/0.67    r2_hidden(sK6(sK4,sK1,sK3),k1_relat_1(sK3)) | ~spl9_2),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f74,f98,f38])).
% 0.38/0.67  fof(f38,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f18])).
% 0.38/0.67  fof(f175,plain,(
% 0.38/0.67    r1_tarski(k1_relat_1(sK3),sK2)),
% 0.38/0.67    inference(backward_demodulation,[],[f88,f162])).
% 0.38/0.67  fof(f162,plain,(
% 0.38/0.67    sK2 = k1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f121,f157,f49])).
% 0.38/0.67  fof(f49,plain,(
% 0.38/0.67    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.38/0.67    inference(cnf_transformation,[],[f24])).
% 0.38/0.67  fof(f24,plain,(
% 0.38/0.67    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.38/0.67    inference(ennf_transformation,[],[f11])).
% 0.38/0.67  fof(f11,axiom,(
% 0.38/0.67    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.38/0.67  fof(f157,plain,(
% 0.38/0.67    k1_xboole_0 != sK0),
% 0.38/0.67    inference(superposition,[],[f59,f70])).
% 0.38/0.67  fof(f70,plain,(
% 0.38/0.67    sK0 = k2_xboole_0(k1_tarski(sK7(sK0)),sK0)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f63,f60])).
% 0.38/0.67  fof(f60,plain,(
% 0.38/0.67    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f28])).
% 0.38/0.67  fof(f28,plain,(
% 0.38/0.67    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.38/0.67    inference(ennf_transformation,[],[f4])).
% 0.38/0.67  fof(f4,axiom,(
% 0.38/0.67    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.38/0.67  fof(f63,plain,(
% 0.38/0.67    r2_hidden(sK7(sK0),sK0)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f37,f52])).
% 0.38/0.67  fof(f52,plain,(
% 0.38/0.67    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f1])).
% 0.38/0.67  fof(f1,axiom,(
% 0.38/0.67    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.38/0.67  fof(f37,plain,(
% 0.38/0.67    ~v1_xboole_0(sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f59,plain,(
% 0.38/0.67    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.38/0.67    inference(cnf_transformation,[],[f5])).
% 0.38/0.67  fof(f5,axiom,(
% 0.38/0.67    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.38/0.67  fof(f121,plain,(
% 0.38/0.67    k1_xboole_0 != sK2),
% 0.38/0.67    inference(superposition,[],[f59,f64])).
% 0.38/0.67  fof(f64,plain,(
% 0.38/0.67    sK2 = k2_xboole_0(k1_tarski(sK7(sK2)),sK2)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f61,f60])).
% 0.38/0.67  fof(f61,plain,(
% 0.38/0.67    r2_hidden(sK7(sK2),sK2)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f35,f52])).
% 0.38/0.67  fof(f35,plain,(
% 0.38/0.67    ~v1_xboole_0(sK2)),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f88,plain,(
% 0.38/0.67    r1_tarski(k1_relat_1(sK3),k1_relat_1(k2_zfmisc_1(sK2,sK0)))),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f74,f51,f75,f54])).
% 0.38/0.67  fof(f54,plain,(
% 0.38/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f26])).
% 0.38/0.67  fof(f26,plain,(
% 0.38/0.67    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.38/0.67    inference(flattening,[],[f25])).
% 0.38/0.67  fof(f25,plain,(
% 0.38/0.67    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f13])).
% 0.38/0.67  fof(f13,axiom,(
% 0.38/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.38/0.67  fof(f75,plain,(
% 0.38/0.67    r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f34,f47])).
% 0.38/0.67  fof(f47,plain,(
% 0.38/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f7])).
% 0.38/0.67  fof(f7,axiom,(
% 0.38/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.38/0.67  fof(f153,plain,(
% 0.38/0.67    spl9_5 | ~spl9_2),
% 0.38/0.67    inference(avatar_split_clause,[],[f76,f96,f151])).
% 0.38/0.67  fof(f76,plain,(
% 0.38/0.67    ( ! [X5] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1)) )),
% 0.38/0.67    inference(backward_demodulation,[],[f29,f73])).
% 0.38/0.67  fof(f73,plain,(
% 0.38/0.67    ( ! [X0] : (k7_relset_1(sK2,sK0,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f34,f45])).
% 0.38/0.67  fof(f45,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f22])).
% 0.38/0.67  fof(f22,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(ennf_transformation,[],[f14])).
% 0.38/0.67  fof(f14,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.38/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.38/0.67  fof(f29,plain,(
% 0.38/0.67    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f134,plain,(
% 0.38/0.67    spl9_4 | spl9_2),
% 0.38/0.67    inference(avatar_split_clause,[],[f78,f96,f131])).
% 0.38/0.67  fof(f78,plain,(
% 0.38/0.67    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.38/0.67    inference(backward_demodulation,[],[f31,f73])).
% 0.38/0.67  fof(f31,plain,(
% 0.38/0.67    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  fof(f115,plain,(
% 0.38/0.67    spl9_3 | spl9_2),
% 0.38/0.67    inference(avatar_split_clause,[],[f79,f96,f112])).
% 0.38/0.67  fof(f79,plain,(
% 0.38/0.67    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.38/0.67    inference(backward_demodulation,[],[f32,f73])).
% 0.38/0.67  fof(f32,plain,(
% 0.38/0.67    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.38/0.67    inference(cnf_transformation,[],[f17])).
% 0.38/0.67  % SZS output end Proof for theBenchmark
% 0.38/0.67  % (31193)------------------------------
% 0.38/0.67  % (31193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.67  % (31193)Termination reason: Refutation
% 0.38/0.67  
% 0.38/0.67  % (31193)Memory used [KB]: 6396
% 0.38/0.67  % (31193)Time elapsed: 0.103 s
% 0.38/0.67  % (31193)------------------------------
% 0.38/0.67  % (31193)------------------------------
% 0.38/0.67  % (31190)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.38/0.68  % (31208)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.38/0.68  % (31195)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.38/0.68  % (31192)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.38/0.68  % (31202)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.38/0.69  % (31212)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.38/0.69  % (31213)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.38/0.69  % (31191)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.38/0.69  % (31204)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.38/0.69  % (31194)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.38/0.69  % (31210)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.38/0.69  % (30960)Success in time 0.333 s
%------------------------------------------------------------------------------
