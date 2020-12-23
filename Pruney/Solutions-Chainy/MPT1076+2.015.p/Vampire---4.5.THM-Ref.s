%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 323 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   32
%              Number of atoms          :  418 (1954 expanded)
%              Number of equality atoms :   32 ( 180 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f176,f184,f219])).

fof(f219,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f217,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f217,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f214,f52])).

fof(f52,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f214,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f193,f31])).

fof(f31,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK4,X0)
        | ~ v4_relat_1(sK4,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f192,f54])).

fof(f54,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f192,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v4_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4)
        | ~ v1_partfun1(sK4,X0) )
    | ~ spl6_6 ),
    inference(superposition,[],[f114,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f114,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_6
  <=> v1_xboole_0(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f184,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f182,f57])).

fof(f57,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f37,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f182,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f179,f52])).

fof(f179,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | spl6_8 ),
    inference(resolution,[],[f157,f31])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK4,X0)
        | ~ v4_relat_1(sK4,X0)
        | ~ v5_relat_1(sK3,X0) )
    | spl6_8 ),
    inference(subsumption_resolution,[],[f156,f54])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v4_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4)
        | ~ v1_partfun1(sK4,X0) )
    | spl6_8 ),
    inference(superposition,[],[f139,f44])).

fof(f139,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_8
  <=> v5_relat_1(sK3,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f176,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f174,f30])).

fof(f30,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f174,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f173,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f173,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl6_7 ),
    inference(resolution,[],[f172,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f172,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f169,f56])).

% (3995)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f56,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f37,f47])).

fof(f169,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | ~ r2_hidden(sK5,sK1)
    | spl6_7 ),
    inference(resolution,[],[f153,f62])).

fof(f62,plain,(
    v1_partfun1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f61,f36])).

fof(f36,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f59,f39])).

fof(f59,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1) ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0)
        | ~ r2_hidden(sK5,X0) )
    | spl6_7 ),
    inference(subsumption_resolution,[],[f143,f58])).

fof(f58,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f37,f46])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X0) )
    | spl6_7 ),
    inference(superposition,[],[f135,f44])).

fof(f135,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_7
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f140,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f131,f112,f137,f133])).

fof(f131,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl6_6 ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f130,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f128,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(resolution,[],[f126,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f126,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_6 ),
    inference(subsumption_resolution,[],[f124,f113])).

fof(f113,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f124,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    inference(resolution,[],[f120,f42])).

fof(f120,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f119,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f118,f30])).

fof(f118,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f117,f37])).

fof(f117,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f116,f36])).

fof(f116,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f105,f35])).

fof(f105,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f103,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f103,plain,(
    ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f102,f54])).

fof(f102,plain,
    ( ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f101,f33])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,
    ( ~ v1_funct_1(sK4)
    | ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f53,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f34,f48])).

fof(f95,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f73,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f73,plain,(
    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f72,f39])).

fof(f72,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f71,f31])).

fof(f71,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f69,f34])).

fof(f69,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f68,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f67,f37])).

fof(f67,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f66,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f63,f38])).

fof(f63,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X1)
      | ~ v1_partfun1(X4,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

fof(f32,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (3982)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (3987)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (3982)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (3998)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f140,f176,f184,f219])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ~spl6_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f218])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    $false | ~spl6_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f217,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | ~spl6_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f214,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    v4_relat_1(sK4,sK0)),
% 0.20/0.48    inference(resolution,[],[f34,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    ~v4_relat_1(sK4,sK0) | v1_xboole_0(sK0) | ~spl6_6),
% 0.20/0.48    inference(resolution,[],[f193,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v1_partfun1(sK4,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0) | v1_xboole_0(X0)) ) | ~spl6_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f192,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    v1_relat_1(sK4)),
% 0.20/0.48    inference(resolution,[],[f34,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ( ! [X0] : (v1_xboole_0(X0) | ~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4) | ~v1_partfun1(sK4,X0)) ) | ~spl6_6),
% 0.20/0.48    inference(superposition,[],[f114,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_partfun1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    v1_xboole_0(k1_relat_1(sK4)) | ~spl6_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl6_6 <=> v1_xboole_0(k1_relat_1(sK4))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    spl6_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    $false | spl6_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    v5_relat_1(sK3,sK0)),
% 0.20/0.48    inference(resolution,[],[f37,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ~v5_relat_1(sK3,sK0) | spl6_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f179,f52])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    ~v4_relat_1(sK4,sK0) | ~v5_relat_1(sK3,sK0) | spl6_8),
% 0.20/0.48    inference(resolution,[],[f157,f31])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0) | ~v5_relat_1(sK3,X0)) ) | spl6_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f156,f54])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4) | ~v1_partfun1(sK4,X0)) ) | spl6_8),
% 0.20/0.48    inference(superposition,[],[f139,f44])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ~v5_relat_1(sK3,k1_relat_1(sK4)) | spl6_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f137])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl6_8 <=> v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    spl6_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    $false | spl6_7),
% 0.20/0.48    inference(subsumption_resolution,[],[f174,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    m1_subset_1(sK5,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,sK1) | spl6_7),
% 0.20/0.48    inference(subsumption_resolution,[],[f173,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl6_7),
% 0.20/0.48    inference(resolution,[],[f172,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ~r2_hidden(sK5,sK1) | spl6_7),
% 0.20/0.48    inference(subsumption_resolution,[],[f169,f56])).
% 0.20/0.48  % (3995)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    v4_relat_1(sK3,sK1)),
% 0.20/0.48    inference(resolution,[],[f37,f47])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ~v4_relat_1(sK3,sK1) | ~r2_hidden(sK5,sK1) | spl6_7),
% 0.20/0.48    inference(resolution,[],[f153,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    v1_partfun1(sK3,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f61,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f60,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f59,f39])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1)),
% 0.20/0.48    inference(resolution,[],[f37,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0) | ~r2_hidden(sK5,X0)) ) | spl6_7),
% 0.20/0.48    inference(subsumption_resolution,[],[f143,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f37,f46])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK5,X0) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X0)) ) | spl6_7),
% 0.20/0.48    inference(superposition,[],[f135,f44])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ~r2_hidden(sK5,k1_relat_1(sK3)) | spl6_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl6_7 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~spl6_7 | ~spl6_8 | spl6_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f131,f112,f137,f133])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ~v5_relat_1(sK3,k1_relat_1(sK4)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | spl6_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f58])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~v5_relat_1(sK3,k1_relat_1(sK4)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl6_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f128,f35])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~v5_relat_1(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl6_6),
% 0.20/0.48    inference(resolution,[],[f126,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ~m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl6_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f124,f113])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_relat_1(sK4)) | spl6_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f112])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    v1_xboole_0(k1_relat_1(sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.48    inference(resolution,[],[f120,f42])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.48    inference(subsumption_resolution,[],[f119,f38])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f118,f30])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f117,f37])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f116,f36])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f35])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(superposition,[],[f103,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.48    inference(subsumption_resolution,[],[f102,f54])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    v1_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ~v1_funct_1(sK4) | ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    v5_relat_1(sK4,sK2)),
% 0.20/0.48    inference(resolution,[],[f34,f48])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~v5_relat_1(sK4,sK2) | ~v1_funct_1(sK4) | ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v5_relat_1(sK4,sK2) | ~v1_funct_1(sK4) | ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.48    inference(superposition,[],[f73,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f72,f39])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f71,f31])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f70,f30])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f69,f34])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f68,f33])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f67,f37])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f66,f36])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f65,f35])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f63,f38])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0)),
% 0.20/0.48    inference(superposition,[],[f32,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (3982)------------------------------
% 0.20/0.48  % (3982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3982)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (3982)Memory used [KB]: 10618
% 0.20/0.48  % (3982)Time elapsed: 0.057 s
% 0.20/0.48  % (3982)------------------------------
% 0.20/0.48  % (3982)------------------------------
% 0.20/0.48  % (3980)Success in time 0.121 s
%------------------------------------------------------------------------------
