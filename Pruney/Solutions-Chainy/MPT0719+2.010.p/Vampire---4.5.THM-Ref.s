%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 186 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f56,f73,f86])).

fof(f86,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f22])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f31,f58])).

fof(f58,plain,(
    k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f54,f22])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = sK3(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3(k1_zfmisc_1(X1)))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f32,f31])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f62,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_4
  <=> ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f73,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f72,f61,f41,f38])).

fof(f38,plain,
    ( spl4_1
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f41,plain,
    ( spl4_2
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f19,f20,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f70,f23])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v5_funct_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f28,f32])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f49,f22])).

fof(f49,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_2 ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f53,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f47,f22])).

fof(f47,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_1 ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f39,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:39:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (23255)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.48  % (23246)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (23246)Refutation not found, incomplete strategy% (23246)------------------------------
% 0.20/0.48  % (23246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23246)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23246)Memory used [KB]: 6012
% 0.20/0.48  % (23246)Time elapsed: 0.004 s
% 0.20/0.48  % (23246)------------------------------
% 0.20/0.48  % (23246)------------------------------
% 0.20/0.48  % (23242)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.48  % (23242)Refutation not found, incomplete strategy% (23242)------------------------------
% 0.20/0.48  % (23242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23242)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23242)Memory used [KB]: 10490
% 0.20/0.48  % (23242)Time elapsed: 0.070 s
% 0.20/0.48  % (23242)------------------------------
% 0.20/0.48  % (23242)------------------------------
% 0.20/0.49  % (23251)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (23251)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f53,f56,f73,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~spl4_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    $false | ~spl4_4),
% 0.20/0.49    inference(resolution,[],[f84,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 0.20/0.49    inference(resolution,[],[f62,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    inference(superposition,[],[f31,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    inference(resolution,[],[f54,f22])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = sK3(k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(resolution,[],[f33,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK3(k1_zfmisc_1(X1))) | ~v1_xboole_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f32,f31])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl4_4 <=> ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f61,f41,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl4_1 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl4_2 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(global_subsumption,[],[f19,f20,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f70,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f35,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v5_funct_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.49    inference(resolution,[],[f28,f32])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    v1_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    $false | spl4_2),
% 0.20/0.49    inference(resolution,[],[f49,f22])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | spl4_2),
% 0.20/0.49    inference(resolution,[],[f42,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~v1_relat_1(k1_xboole_0) | spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f41])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    $false | spl4_1),
% 0.20/0.49    inference(resolution,[],[f47,f22])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | spl4_1),
% 0.20/0.49    inference(resolution,[],[f39,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~v1_funct_1(k1_xboole_0) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f38])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (23251)------------------------------
% 0.20/0.49  % (23251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23251)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (23251)Memory used [KB]: 10618
% 0.20/0.49  % (23251)Time elapsed: 0.087 s
% 0.20/0.49  % (23251)------------------------------
% 0.20/0.49  % (23251)------------------------------
% 0.20/0.50  % (23235)Success in time 0.133 s
%------------------------------------------------------------------------------
