%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 297 expanded)
%              Number of leaves         :   22 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  278 ( 894 expanded)
%              Number of equality atoms :   80 ( 324 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12449)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (12464)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (12467)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (12475)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (12459)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (12474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (12457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (12457)Refutation not found, incomplete strategy% (12457)------------------------------
% (12457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12457)Termination reason: Refutation not found, incomplete strategy

% (12457)Memory used [KB]: 10746
% (12457)Time elapsed: 0.158 s
% (12457)------------------------------
% (12457)------------------------------
% (12456)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (12472)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f189,f232,f343])).

fof(f343,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f273,f336,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f336,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f335,f290])).

fof(f290,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f257,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f272,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f272,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f236,f238])).

fof(f238,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f133,f43])).

fof(f133,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f236,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f133,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f257,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f211,f238])).

fof(f211,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f180,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f180,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f117,f121])).

fof(f121,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f96,f118,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f118,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f96,f92,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f92,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f40,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f55,f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f108,f67])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f108,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f56,f96,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f335,plain,
    ( ~ v1_xboole_0(k10_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f334,f263])).

fof(f263,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f218,f238])).

fof(f218,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f195,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f195,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,k1_xboole_0,sK2,X0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f95,f84])).

fof(f95,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f334,plain,
    ( ~ v1_xboole_0(k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f262,f43])).

fof(f262,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f217,f238])).

fof(f217,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f193,f81])).

fof(f193,plain,
    ( sK0 != k8_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f41,f84])).

fof(f41,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f273,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f235,f238])).

% (12473)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f235,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f133,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f232,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f50,f207])).

fof(f207,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_2
    | spl5_3 ),
    inference(backward_demodulation,[],[f155,f84])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_3 ),
    inference(resolution,[],[f151,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

% (12468)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f151,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f142,f70])).

fof(f142,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(sK0,sK1))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f97,f140,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f140,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f134,f69])).

fof(f134,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f97,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f189,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f147,f184])).

fof(f184,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | spl5_2 ),
    inference(forward_demodulation,[],[f180,f105])).

fof(f105,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f93,f94])).

fof(f94,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f85,f39,f40,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (12450)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (12465)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f93,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f147,plain,(
    sK0 != k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f41,f95])).

fof(f86,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f37,f83,f79])).

fof(f37,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:57:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (12455)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (12471)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (12470)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (12453)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (12463)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (12462)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (12454)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (12455)Refutation not found, incomplete strategy% (12455)------------------------------
% 0.22/0.55  % (12455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (12461)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (12455)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12455)Memory used [KB]: 10746
% 0.22/0.56  % (12455)Time elapsed: 0.122 s
% 0.22/0.56  % (12455)------------------------------
% 0.22/0.56  % (12455)------------------------------
% 0.22/0.56  % (12451)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (12469)Refutation not found, incomplete strategy% (12469)------------------------------
% 0.22/0.56  % (12469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12469)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12469)Memory used [KB]: 10874
% 0.22/0.56  % (12469)Time elapsed: 0.122 s
% 0.22/0.56  % (12469)------------------------------
% 0.22/0.56  % (12469)------------------------------
% 0.22/0.57  % (12451)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  % (12449)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.57  % (12464)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.57  % (12467)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.58  % (12475)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.58  % (12459)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.58  % (12474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.73/0.58  % (12457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.73/0.59  % (12457)Refutation not found, incomplete strategy% (12457)------------------------------
% 1.73/0.59  % (12457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (12457)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (12457)Memory used [KB]: 10746
% 1.73/0.59  % (12457)Time elapsed: 0.158 s
% 1.73/0.59  % (12457)------------------------------
% 1.73/0.59  % (12457)------------------------------
% 1.73/0.59  % (12456)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.73/0.59  % (12472)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.73/0.59  fof(f344,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(avatar_sat_refutation,[],[f86,f189,f232,f343])).
% 1.73/0.59  fof(f343,plain,(
% 1.73/0.59    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f339])).
% 1.73/0.59  fof(f339,plain,(
% 1.73/0.59    $false | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f273,f336,f69])).
% 1.73/0.59  fof(f69,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f1])).
% 1.73/0.59  fof(f1,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.73/0.59  fof(f336,plain,(
% 1.73/0.59    ~v1_xboole_0(k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(forward_demodulation,[],[f335,f290])).
% 1.73/0.59  fof(f290,plain,(
% 1.73/0.59    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(backward_demodulation,[],[f257,f286])).
% 1.73/0.59  fof(f286,plain,(
% 1.73/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f272,f43])).
% 1.73/0.59  fof(f43,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f24])).
% 1.73/0.59  fof(f24,plain,(
% 1.73/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.73/0.59  fof(f272,plain,(
% 1.73/0.59    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl5_3),
% 1.73/0.59    inference(forward_demodulation,[],[f236,f238])).
% 1.73/0.59  fof(f238,plain,(
% 1.73/0.59    k1_xboole_0 = sK2 | ~spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f133,f43])).
% 1.73/0.59  fof(f133,plain,(
% 1.73/0.59    v1_xboole_0(sK2) | ~spl5_3),
% 1.73/0.59    inference(avatar_component_clause,[],[f132])).
% 1.73/0.59  fof(f132,plain,(
% 1.73/0.59    spl5_3 <=> v1_xboole_0(sK2)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.73/0.59  fof(f236,plain,(
% 1.73/0.59    v1_xboole_0(k1_relat_1(sK2)) | ~spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f133,f59])).
% 1.73/0.59  fof(f59,plain,(
% 1.73/0.59    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f30])).
% 1.73/0.59  fof(f30,plain,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f9])).
% 1.73/0.59  fof(f9,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.73/0.59  fof(f257,plain,(
% 1.73/0.59    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(backward_demodulation,[],[f211,f238])).
% 1.73/0.59  fof(f211,plain,(
% 1.73/0.59    k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0) | ~spl5_2),
% 1.73/0.59    inference(backward_demodulation,[],[f180,f84])).
% 1.73/0.59  fof(f84,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~spl5_2),
% 1.73/0.59    inference(avatar_component_clause,[],[f83])).
% 1.73/0.59  fof(f83,plain,(
% 1.73/0.59    spl5_2 <=> k1_xboole_0 = sK1),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.73/0.59  fof(f180,plain,(
% 1.73/0.59    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 1.73/0.59    inference(superposition,[],[f117,f121])).
% 1.73/0.59  fof(f121,plain,(
% 1.73/0.59    sK2 = k5_relat_1(sK2,k6_relat_1(sK1))),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f96,f118,f66])).
% 1.73/0.59  fof(f66,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.73/0.59    inference(flattening,[],[f34])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,axiom,(
% 1.73/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.73/0.59  fof(f118,plain,(
% 1.73/0.59    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f96,f92,f65])).
% 1.73/0.59  fof(f65,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f33])).
% 1.73/0.59  fof(f33,plain,(
% 1.73/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f8])).
% 1.73/0.59  fof(f8,axiom,(
% 1.73/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.73/0.59  fof(f92,plain,(
% 1.73/0.59    v5_relat_1(sK2,sK1)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f40,f72])).
% 1.73/0.59  fof(f72,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f36])).
% 1.73/0.59  fof(f36,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.59    inference(ennf_transformation,[],[f15])).
% 1.73/0.59  fof(f15,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.73/0.59  fof(f40,plain,(
% 1.73/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  fof(f22,plain,(
% 1.73/0.59    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.73/0.59    inference(flattening,[],[f21])).
% 1.73/0.59  fof(f21,plain,(
% 1.73/0.59    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.73/0.59    inference(ennf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,negated_conjecture,(
% 1.73/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.73/0.59    inference(negated_conjecture,[],[f19])).
% 1.73/0.59  fof(f19,conjecture,(
% 1.73/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 1.73/0.59  fof(f96,plain,(
% 1.73/0.59    v1_relat_1(sK2)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f55,f40,f53])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f27])).
% 1.73/0.59  fof(f27,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f7])).
% 1.73/0.59  fof(f7,axiom,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.73/0.59  fof(f55,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f10])).
% 1.73/0.59  fof(f10,axiom,(
% 1.73/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.73/0.59  fof(f117,plain,(
% 1.73/0.59    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) )),
% 1.73/0.59    inference(forward_demodulation,[],[f108,f67])).
% 1.73/0.59  fof(f67,plain,(
% 1.73/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f12])).
% 1.73/0.59  fof(f12,axiom,(
% 1.73/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.73/0.59  fof(f108,plain,(
% 1.73/0.59    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))) )),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f56,f96,f58])).
% 1.73/0.59  fof(f58,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,axiom,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.73/0.59  fof(f56,plain,(
% 1.73/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f14])).
% 1.73/0.59  fof(f14,axiom,(
% 1.73/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.73/0.59  fof(f335,plain,(
% 1.73/0.59    ~v1_xboole_0(k10_relat_1(k1_xboole_0,k1_xboole_0)) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(forward_demodulation,[],[f334,f263])).
% 1.73/0.59  fof(f263,plain,(
% 1.73/0.59    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(backward_demodulation,[],[f218,f238])).
% 1.73/0.59  fof(f218,plain,(
% 1.73/0.59    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | (~spl5_1 | ~spl5_2)),
% 1.73/0.59    inference(backward_demodulation,[],[f195,f81])).
% 1.73/0.59  fof(f81,plain,(
% 1.73/0.59    k1_xboole_0 = sK0 | ~spl5_1),
% 1.73/0.59    inference(avatar_component_clause,[],[f79])).
% 1.73/0.59  fof(f79,plain,(
% 1.73/0.59    spl5_1 <=> k1_xboole_0 = sK0),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.73/0.59  fof(f195,plain,(
% 1.73/0.59    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,k1_xboole_0,sK2,X0)) ) | ~spl5_2),
% 1.73/0.59    inference(backward_demodulation,[],[f95,f84])).
% 1.73/0.59  fof(f95,plain,(
% 1.73/0.59    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f40,f42])).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f23])).
% 1.73/0.59  fof(f23,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.59    inference(ennf_transformation,[],[f17])).
% 1.73/0.59  fof(f17,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.73/0.59  fof(f334,plain,(
% 1.73/0.59    ~v1_xboole_0(k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f262,f43])).
% 1.73/0.59  fof(f262,plain,(
% 1.73/0.59    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.73/0.59    inference(backward_demodulation,[],[f217,f238])).
% 1.73/0.59  fof(f217,plain,(
% 1.73/0.59    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 1.73/0.59    inference(backward_demodulation,[],[f193,f81])).
% 1.73/0.59  fof(f193,plain,(
% 1.73/0.59    sK0 != k8_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | ~spl5_2),
% 1.73/0.59    inference(backward_demodulation,[],[f41,f84])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    sK0 != k8_relset_1(sK0,sK1,sK2,sK1)),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  fof(f273,plain,(
% 1.73/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_3),
% 1.73/0.59    inference(forward_demodulation,[],[f235,f238])).
% 1.73/0.59  % (12473)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.73/0.59  fof(f235,plain,(
% 1.73/0.59    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f133,f70])).
% 1.73/0.59  fof(f70,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f1])).
% 1.73/0.59  fof(f232,plain,(
% 1.73/0.59    ~spl5_2 | spl5_3),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f228])).
% 1.73/0.59  fof(f228,plain,(
% 1.73/0.59    $false | (~spl5_2 | spl5_3)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f50,f207])).
% 1.73/0.59  fof(f207,plain,(
% 1.73/0.59    ~v1_xboole_0(k1_xboole_0) | (~spl5_2 | spl5_3)),
% 1.73/0.59    inference(backward_demodulation,[],[f155,f84])).
% 1.73/0.59  fof(f155,plain,(
% 1.73/0.59    ~v1_xboole_0(sK1) | spl5_3),
% 1.73/0.59    inference(resolution,[],[f151,f54])).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f28])).
% 1.73/0.59  fof(f28,plain,(
% 1.73/0.59    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f5])).
% 1.73/0.59  fof(f5,axiom,(
% 1.73/0.59    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.73/0.59  % (12468)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.73/0.59  fof(f151,plain,(
% 1.73/0.59    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f142,f70])).
% 1.73/0.59  fof(f142,plain,(
% 1.73/0.59    r2_hidden(sK4(sK2),k2_zfmisc_1(sK0,sK1)) | spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f97,f140,f61])).
% 1.73/0.59  fof(f61,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f32])).
% 1.73/0.59  fof(f32,plain,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f2])).
% 1.73/0.59  fof(f2,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.73/0.59  fof(f140,plain,(
% 1.73/0.59    r2_hidden(sK4(sK2),sK2) | spl5_3),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f134,f69])).
% 1.73/0.59  fof(f134,plain,(
% 1.73/0.59    ~v1_xboole_0(sK2) | spl5_3),
% 1.73/0.59    inference(avatar_component_clause,[],[f132])).
% 1.73/0.59  fof(f97,plain,(
% 1.73/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f40,f52])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f6])).
% 1.73/0.59  fof(f6,axiom,(
% 1.73/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.73/0.59  fof(f50,plain,(
% 1.73/0.59    v1_xboole_0(k1_xboole_0)),
% 1.73/0.59    inference(cnf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    v1_xboole_0(k1_xboole_0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.73/0.59  fof(f189,plain,(
% 1.73/0.59    spl5_2),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f185])).
% 1.73/0.59  fof(f185,plain,(
% 1.73/0.59    $false | spl5_2),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f147,f184])).
% 1.73/0.59  fof(f184,plain,(
% 1.73/0.59    sK0 = k10_relat_1(sK2,sK1) | spl5_2),
% 1.73/0.59    inference(forward_demodulation,[],[f180,f105])).
% 1.73/0.59  fof(f105,plain,(
% 1.73/0.59    sK0 = k1_relat_1(sK2) | spl5_2),
% 1.73/0.59    inference(forward_demodulation,[],[f93,f94])).
% 1.73/0.59  fof(f94,plain,(
% 1.73/0.59    sK0 = k1_relset_1(sK0,sK1,sK2) | spl5_2),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f85,f39,f40,f49])).
% 1.73/0.59  fof(f49,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f26])).
% 1.73/0.59  % (12450)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.73/0.59  % (12465)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.59    inference(flattening,[],[f25])).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.59    inference(ennf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  fof(f85,plain,(
% 1.73/0.59    k1_xboole_0 != sK1 | spl5_2),
% 1.73/0.59    inference(avatar_component_clause,[],[f83])).
% 1.73/0.59  fof(f93,plain,(
% 1.73/0.59    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f40,f60])).
% 1.73/0.59  fof(f60,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f31])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.59    inference(ennf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.73/0.59  fof(f147,plain,(
% 1.73/0.59    sK0 != k10_relat_1(sK2,sK1)),
% 1.73/0.59    inference(superposition,[],[f41,f95])).
% 1.73/0.59  fof(f86,plain,(
% 1.73/0.59    spl5_1 | ~spl5_2),
% 1.73/0.59    inference(avatar_split_clause,[],[f37,f83,f79])).
% 1.73/0.59  fof(f37,plain,(
% 1.73/0.59    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  % SZS output end Proof for theBenchmark
% 1.73/0.59  % (12451)------------------------------
% 1.73/0.59  % (12451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (12449)Refutation not found, incomplete strategy% (12449)------------------------------
% 1.73/0.59  % (12449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (12451)Termination reason: Refutation
% 1.73/0.59  
% 1.73/0.59  % (12451)Memory used [KB]: 6396
% 1.73/0.59  % (12451)Time elapsed: 0.139 s
% 1.73/0.59  % (12451)------------------------------
% 1.73/0.59  % (12451)------------------------------
% 1.73/0.59  % (12449)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (12449)Memory used [KB]: 10746
% 1.73/0.59  % (12449)Time elapsed: 0.163 s
% 1.73/0.59  % (12449)------------------------------
% 1.73/0.59  % (12449)------------------------------
% 1.73/0.60  % (12446)Success in time 0.228 s
%------------------------------------------------------------------------------
