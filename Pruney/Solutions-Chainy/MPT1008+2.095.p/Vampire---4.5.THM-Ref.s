%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 118 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  169 ( 382 expanded)
%              Number of equality atoms :   64 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f105,f115])).

fof(f115,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f62,f109])).

fof(f109,plain,
    ( ~ r2_hidden(k2_relat_1(sK2),k1_tarski(k2_relat_1(sK2)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f82,f108])).

fof(f108,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f106,f84])).

fof(f84,plain,(
    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f71,f66,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (7837)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f66,plain,(
    v4_relat_1(sK2,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f46,f30,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f106,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k1_tarski(sK0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f62,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f82,plain,(
    ~ r2_hidden(k2_relat_1(sK2),k1_tarski(k1_tarski(k1_funct_1(sK2,sK0)))) ),
    inference(unit_resulting_resolution,[],[f78,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f78,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f32,f70])).

fof(f70,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f32,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f105,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f46,f30,f90,f45])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f94,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f80,f92,f88])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_relat_1(sK2)
      | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    inference(backward_demodulation,[],[f63,f79])).

fof(f79,plain,(
    k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f68,f69])).

% (7840)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f69,plain,(
    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f31,f29,f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f29,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f30,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

% (7855)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (7838)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.48  % (7838)Refutation not found, incomplete strategy% (7838)------------------------------
% 0.20/0.48  % (7838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7838)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7838)Memory used [KB]: 1791
% 0.20/0.48  % (7838)Time elapsed: 0.082 s
% 0.20/0.48  % (7838)------------------------------
% 0.20/0.48  % (7838)------------------------------
% 0.20/0.51  % (7860)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (7852)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (7862)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (7862)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (7842)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (7854)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (7844)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (7846)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (7848)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (7849)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (7850)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f94,f105,f115])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ~spl5_2),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    $false | ~spl5_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f62,f109])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ~r2_hidden(k2_relat_1(sK2),k1_tarski(k2_relat_1(sK2))) | ~spl5_2),
% 0.20/0.54    inference(backward_demodulation,[],[f82,f108])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~spl5_2),
% 0.20/0.54    inference(forward_demodulation,[],[f106,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    sK2 = k7_relat_1(sK2,k1_tarski(sK0))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f71,f66,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  % (7837)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    v4_relat_1(sK2,k1_tarski(sK0))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f30,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f13])).
% 0.20/0.54  fof(f13,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f46,f30,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k1_tarski(sK0))) | ~spl5_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f62,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0))) ) | ~spl5_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    spl5_2 <=> ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ~r2_hidden(k2_relat_1(sK2),k1_tarski(k1_tarski(k1_funct_1(sK2,sK0))))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f78,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.20/0.54    inference(equality_resolution,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f32,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f30,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.20/0.54    inference(equality_resolution,[],[f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.20/0.54    inference(equality_resolution,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    spl5_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f100])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    $false | spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f46,f30,f90,f45])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl5_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    spl5_1 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ~spl5_1 | spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f80,f92,f88])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~v1_relat_1(sK2) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0))) )),
% 0.20/0.54    inference(backward_demodulation,[],[f63,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    k1_tarski(sK0) = k1_relat_1(sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f68,f69])).
% 0.20/0.54  % (7840)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f31,f29,f30,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f30,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  % (7855)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0))) )),
% 0.20/0.54    inference(resolution,[],[f28,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (7862)------------------------------
% 0.20/0.54  % (7862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7862)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (7862)Memory used [KB]: 6268
% 0.20/0.54  % (7862)Time elapsed: 0.122 s
% 0.20/0.54  % (7862)------------------------------
% 0.20/0.54  % (7862)------------------------------
% 0.20/0.54  % (7836)Success in time 0.181 s
%------------------------------------------------------------------------------
