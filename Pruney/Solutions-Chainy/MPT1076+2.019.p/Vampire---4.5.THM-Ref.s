%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 331 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  472 (2085 expanded)
%              Number of equality atoms :   53 ( 209 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f120,f127,f134,f160,f184,f197,f225])).

fof(f225,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f210,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f210,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f49,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

% (31926)Refutation not found, incomplete strategy% (31926)------------------------------
% (31926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31926)Termination reason: Refutation not found, incomplete strategy

% (31926)Memory used [KB]: 10618
% (31926)Time elapsed: 0.076 s
% (31926)------------------------------
% (31926)------------------------------
% (31919)Refutation not found, incomplete strategy% (31919)------------------------------
% (31919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31919)Termination reason: Refutation not found, incomplete strategy

% (31919)Memory used [KB]: 1918
% (31919)Time elapsed: 0.056 s
% (31919)------------------------------
% (31919)------------------------------
% (31922)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (31925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (31924)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (31906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (31914)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (31923)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f197,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f195,f49])).

fof(f195,plain,
    ( v1_xboole_0(sK1)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f194,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f194,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f193,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f192,f47])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f192,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f191,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f191,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | spl6_8 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | spl6_8 ),
    inference(superposition,[],[f159,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f159,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_8
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f184,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f182,f81])).

fof(f81,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f182,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f179,f73])).

fof(f73,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f179,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | spl6_7 ),
    inference(resolution,[],[f174,f42])).

fof(f42,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK4,X0)
        | ~ v4_relat_1(sK4,X0)
        | ~ v5_relat_1(sK3,X0) )
    | spl6_7 ),
    inference(subsumption_resolution,[],[f173,f79])).

fof(f79,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f76,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f173,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v4_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4)
        | ~ v1_partfun1(sK4,X0) )
    | spl6_7 ),
    inference(superposition,[],[f171,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f171,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | spl6_7 ),
    inference(subsumption_resolution,[],[f169,f84])).

fof(f84,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f83,f54])).

fof(f83,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f48,f53])).

fof(f169,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | spl6_7 ),
    inference(resolution,[],[f168,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f168,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | spl6_7 ),
    inference(subsumption_resolution,[],[f166,f45])).

fof(f166,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_7 ),
    inference(superposition,[],[f163,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f163,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
    | spl6_7 ),
    inference(subsumption_resolution,[],[f161,f48])).

fof(f161,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_7 ),
    inference(superposition,[],[f155,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f155,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_7
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f160,plain,
    ( spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_4 ),
    inference(avatar_split_clause,[],[f147,f102,f157,f153,f149])).

fof(f102,plain,
    ( spl6_4
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f147,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | spl6_4 ),
    inference(subsumption_resolution,[],[f146,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f146,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f145,f41])).

fof(f145,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f143,f44])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f142,f48])).

fof(f142,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f141,f47])).

fof(f141,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f140,f46])).

fof(f140,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(superposition,[],[f104,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f104,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f134,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f132,f46])).

fof(f132,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f131,f45])).

fof(f131,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f130,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f129,f48])).

fof(f129,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f128,f47])).

fof(f128,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_1 ),
    inference(resolution,[],[f92,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f92,plain,
    ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_1
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f127,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f125,f46])).

fof(f125,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f124,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f122,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_2 ),
    inference(resolution,[],[f96,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_2
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f120,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f118,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f117,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f116,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f115,f48])).

fof(f115,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f114,f47])).

fof(f114,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | spl6_3 ),
    inference(resolution,[],[f100,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,
    ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_3
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f105,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f88,f102,f98,f94,f90])).

fof(f88,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f87,f49])).

fof(f87,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f85,f41])).

fof(f85,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f43,f68])).

fof(f43,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:36:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (31912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (31920)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (31910)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (31913)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (31921)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (31919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (31918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (31917)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (31915)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (31916)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (31911)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (31908)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (31909)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (31926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (31907)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31907)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f105,f120,f127,f134,f160,f184,f197,f225])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ~spl6_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    $false | ~spl6_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | ~spl6_6),
% 0.21/0.51    inference(backward_demodulation,[],[f49,f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl6_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl6_6 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % (31926)Refutation not found, incomplete strategy% (31926)------------------------------
% 0.21/0.51  % (31926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31926)Memory used [KB]: 10618
% 0.21/0.51  % (31926)Time elapsed: 0.076 s
% 0.21/0.51  % (31926)------------------------------
% 0.21/0.51  % (31926)------------------------------
% 0.21/0.52  % (31919)Refutation not found, incomplete strategy% (31919)------------------------------
% 0.21/0.52  % (31919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31919)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31919)Memory used [KB]: 1918
% 0.21/0.52  % (31919)Time elapsed: 0.056 s
% 0.21/0.52  % (31919)------------------------------
% 0.21/0.52  % (31919)------------------------------
% 0.21/0.52  % (31922)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (31925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (31924)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (31906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (31914)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (31923)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    spl6_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    $false | spl6_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f195,f49])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | spl6_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f194,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    m1_subset_1(sK5,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | spl6_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | spl6_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f192,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | spl6_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | spl6_8),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f189])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | spl6_8),
% 0.21/0.53    inference(superposition,[],[f159,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | spl6_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    spl6_8 <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    spl6_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    $false | spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    v5_relat_1(sK3,sK0)),
% 0.21/0.53    inference(resolution,[],[f48,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~v5_relat_1(sK3,sK0) | spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    v4_relat_1(sK4,sK0)),
% 0.21/0.53    inference(resolution,[],[f45,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ~v4_relat_1(sK4,sK0) | ~v5_relat_1(sK3,sK0) | spl6_7),
% 0.21/0.53    inference(resolution,[],[f174,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v1_partfun1(sK4,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0) | ~v5_relat_1(sK3,X0)) ) | spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f173,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f45,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4) | ~v1_partfun1(sK4,X0)) ) | spl6_7),
% 0.21/0.53    inference(superposition,[],[f171,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_partfun1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ~v5_relat_1(sK3,k1_relat_1(sK4)) | spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f54])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f48,f53])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | ~v5_relat_1(sK3,k1_relat_1(sK4)) | spl6_7),
% 0.21/0.53    inference(resolution,[],[f168,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f166,f45])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_7),
% 0.21/0.53    inference(superposition,[],[f163,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f161,f48])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_7),
% 0.21/0.53    inference(superposition,[],[f155,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | spl6_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f153])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    spl6_7 <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl6_6 | ~spl6_7 | ~spl6_8 | spl6_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f147,f102,f157,f153,f149])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl6_4 <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f41])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f45])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f143,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f142,f48])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f47])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f140,f46])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(superposition,[],[f104,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | spl6_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl6_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    $false | spl6_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f132,f46])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~v1_funct_1(sK3) | spl6_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f131,f45])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f44])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f129,f48])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f128,f47])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_1),
% 0.21/0.54    inference(resolution,[],[f92,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl6_1 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl6_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    $false | spl6_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f46])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ~v1_funct_1(sK3) | spl6_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f45])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f44])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f122,f48])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f121,f47])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_2),
% 0.21/0.54    inference(resolution,[],[f96,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl6_2 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl6_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    $false | spl6_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f118,f46])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~v1_funct_1(sK3) | spl6_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f45])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f116,f44])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f48])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f47])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | spl6_3),
% 0.21/0.54    inference(resolution,[],[f100,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | spl6_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl6_3 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f88,f102,f98,f94,f90])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f87,f49])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f41])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.21/0.54    inference(superposition,[],[f43,f68])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31907)------------------------------
% 0.21/0.54  % (31907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31907)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31907)Memory used [KB]: 10746
% 0.21/0.54  % (31907)Time elapsed: 0.106 s
% 0.21/0.54  % (31907)------------------------------
% 0.21/0.54  % (31907)------------------------------
% 0.21/0.54  % (31905)Success in time 0.178 s
%------------------------------------------------------------------------------
