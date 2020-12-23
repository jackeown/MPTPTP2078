%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:32 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 197 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  175 ( 576 expanded)
%              Number of equality atoms :   57 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f212,f263])).

fof(f263,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f62,f259,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f259,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f68,f256])).

fof(f256,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f37,f62,f244,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f244,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f242,f78])).

fof(f78,plain,(
    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f62,f60,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f60,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f242,plain,
    ( k1_tarski(sK0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(sK0)))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f62,f230,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

% (31132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (31152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (31145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (31143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (31158)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (31133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (31150)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (31142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f230,plain,
    ( r1_tarski(k1_tarski(sK0),k1_relat_1(sK3))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f116,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f5])).

% (31152)Refutation not found, incomplete strategy% (31152)------------------------------
% (31152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f116,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f41,f63])).

fof(f63,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f41,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f39,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f212,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f44,f170])).

fof(f170,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f147,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f147,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_3 ),
    inference(backward_demodulation,[],[f68,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK3
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f62,f131,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f131,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | spl4_3 ),
    inference(backward_demodulation,[],[f88,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k11_relat_1(sK3,sK0)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f62,f117,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f117,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK3))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f88,plain,(
    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    inference(superposition,[],[f72,f83])).

fof(f83,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f71,f78])).

fof(f71,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f62,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f72,plain,(
    ! [X0] : k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f62,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (31130)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (31154)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (31138)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (31130)Refutation not found, incomplete strategy% (31130)------------------------------
% 0.21/0.52  % (31130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31130)Memory used [KB]: 1791
% 0.21/0.52  % (31130)Time elapsed: 0.100 s
% 0.21/0.52  % (31130)------------------------------
% 0.21/0.52  % (31130)------------------------------
% 0.21/0.52  % (31135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (31134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.52  % (31134)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f264,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(avatar_sat_refutation,[],[f212,f263])).
% 1.25/0.52  fof(f263,plain,(
% 1.25/0.52    ~spl4_3),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f261])).
% 1.25/0.52  fof(f261,plain,(
% 1.25/0.52    $false | ~spl4_3),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f62,f259,f43])).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.25/0.52  fof(f259,plain,(
% 1.25/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_3),
% 1.25/0.52    inference(backward_demodulation,[],[f68,f256])).
% 1.25/0.52  fof(f256,plain,(
% 1.25/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_3),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f37,f62,f244,f45])).
% 1.25/0.52  fof(f45,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f26])).
% 1.25/0.52  fof(f26,plain,(
% 1.25/0.52    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.25/0.52  fof(f244,plain,(
% 1.25/0.52    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_3),
% 1.25/0.52    inference(forward_demodulation,[],[f242,f78])).
% 1.25/0.52  fof(f78,plain,(
% 1.25/0.52    sK3 = k7_relat_1(sK3,k1_tarski(sK0))),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f62,f60,f51])).
% 1.25/0.52  fof(f51,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f31])).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f11])).
% 1.25/0.52  fof(f11,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.25/0.52  fof(f60,plain,(
% 1.25/0.52    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f39,f55])).
% 1.25/0.52  fof(f55,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f35])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f16])).
% 1.25/0.52  fof(f16,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.25/0.52    inference(cnf_transformation,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.25/0.52    inference(flattening,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.25/0.52    inference(ennf_transformation,[],[f19])).
% 1.25/0.52  fof(f19,negated_conjecture,(
% 1.25/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.25/0.52    inference(negated_conjecture,[],[f18])).
% 1.25/0.52  fof(f18,conjecture,(
% 1.25/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.25/0.52  fof(f242,plain,(
% 1.25/0.52    k1_tarski(sK0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(sK0))) | ~spl4_3),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f62,f230,f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f13])).
% 1.25/0.52  fof(f13,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.25/0.53  % (31132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (31152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.53  % (31145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.53  % (31143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (31158)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.53  % (31133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.54  % (31150)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.54  % (31142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  fof(f230,plain,(
% 1.25/0.54    r1_tarski(k1_tarski(sK0),k1_relat_1(sK3)) | ~spl4_3),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f116,f58])).
% 1.25/0.54  fof(f58,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f5])).
% 1.41/0.54  % (31152)Refutation not found, incomplete strategy% (31152)------------------------------
% 1.41/0.54  % (31152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.54  fof(f116,plain,(
% 1.41/0.54    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl4_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f115])).
% 1.41/0.54  fof(f115,plain,(
% 1.41/0.54    spl4_3 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    v1_funct_1(sK3)),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  fof(f68,plain,(
% 1.41/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.41/0.54    inference(backward_demodulation,[],[f41,f63])).
% 1.41/0.54  fof(f63,plain,(
% 1.41/0.54    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f39,f46])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f27])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f17])).
% 1.41/0.54  fof(f17,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  fof(f62,plain,(
% 1.41/0.54    v1_relat_1(sK3)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f39,f50])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.54  fof(f212,plain,(
% 1.41/0.54    spl4_3),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f209])).
% 1.41/0.54  fof(f209,plain,(
% 1.41/0.54    $false | spl4_3),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f44,f170])).
% 1.41/0.54  fof(f170,plain,(
% 1.41/0.54    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_3),
% 1.41/0.54    inference(forward_demodulation,[],[f147,f49])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 1.41/0.54  fof(f147,plain,(
% 1.41/0.54    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_3),
% 1.41/0.54    inference(backward_demodulation,[],[f68,f136])).
% 1.41/0.54  fof(f136,plain,(
% 1.41/0.54    k1_xboole_0 = sK3 | spl4_3),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f62,f131,f48])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f28])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,axiom,(
% 1.41/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.41/0.54  fof(f131,plain,(
% 1.41/0.54    k1_xboole_0 = k2_relat_1(sK3) | spl4_3),
% 1.41/0.54    inference(backward_demodulation,[],[f88,f128])).
% 1.41/0.54  fof(f128,plain,(
% 1.41/0.54    k1_xboole_0 = k11_relat_1(sK3,sK0) | spl4_3),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f62,f117,f53])).
% 1.41/0.54  fof(f53,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f34])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f10])).
% 1.41/0.54  fof(f10,axiom,(
% 1.41/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 1.41/0.54  fof(f117,plain,(
% 1.41/0.54    ~r2_hidden(sK0,k1_relat_1(sK3)) | spl4_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f115])).
% 1.41/0.54  fof(f88,plain,(
% 1.41/0.54    k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 1.41/0.54    inference(superposition,[],[f72,f83])).
% 1.41/0.54  fof(f83,plain,(
% 1.41/0.54    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))),
% 1.41/0.54    inference(superposition,[],[f71,f78])).
% 1.41/0.54  fof(f71,plain,(
% 1.41/0.54    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f62,f52])).
% 1.41/0.54  fof(f52,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f33])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.41/0.54  fof(f72,plain,(
% 1.41/0.54    ( ! [X0] : (k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0))) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f62,f57])).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.41/0.54  fof(f44,plain,(
% 1.41/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (31134)------------------------------
% 1.41/0.54  % (31134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (31134)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (31134)Memory used [KB]: 6268
% 1.41/0.54  % (31134)Time elapsed: 0.112 s
% 1.41/0.54  % (31134)------------------------------
% 1.41/0.54  % (31134)------------------------------
% 1.41/0.54  % (31152)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (31152)Memory used [KB]: 10746
% 1.41/0.54  % (31152)Time elapsed: 0.133 s
% 1.41/0.54  % (31152)------------------------------
% 1.41/0.54  % (31152)------------------------------
% 1.41/0.54  % (31129)Success in time 0.177 s
%------------------------------------------------------------------------------
