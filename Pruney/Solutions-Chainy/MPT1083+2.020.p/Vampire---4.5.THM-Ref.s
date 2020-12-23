%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:19 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 445 expanded)
%              Number of equality atoms :   30 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (27941)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f42,f58,f70,f74,f79])).

fof(f79,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl3_6 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(superposition,[],[f22,f69])).

fof(f69,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_6
  <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f22,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

fof(f74,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f66,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f63,f56,f68,f65])).

fof(f56,plain,
    ( spl3_3
  <=> ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f57,f20])).

fof(f20,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f52,f56,f35])).

fof(f35,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v5_relat_1(X0,sK0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f47,f50])).

fof(f50,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(global_subsumption,[],[f23,f24,f49])).

fof(f49,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(forward_demodulation,[],[f48,f45])).

fof(f45,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f48,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f24,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f39,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f38,f35])).

fof(f33,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (27944)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (27936)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.14/0.52  % (27942)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.14/0.52  % (27944)Refutation found. Thanks to Tanya!
% 1.14/0.52  % SZS status Theorem for theBenchmark
% 1.14/0.52  % SZS output start Proof for theBenchmark
% 1.14/0.52  % (27941)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.14/0.52  fof(f80,plain,(
% 1.14/0.52    $false),
% 1.14/0.52    inference(avatar_sat_refutation,[],[f40,f42,f58,f70,f74,f79])).
% 1.14/0.52  fof(f79,plain,(
% 1.14/0.52    ~spl3_6),
% 1.14/0.52    inference(avatar_contradiction_clause,[],[f78])).
% 1.14/0.52  fof(f78,plain,(
% 1.14/0.52    $false | ~spl3_6),
% 1.14/0.52    inference(trivial_inequality_removal,[],[f75])).
% 1.14/0.52  fof(f75,plain,(
% 1.14/0.52    k1_relat_1(sK2) != k1_relat_1(sK2) | ~spl3_6),
% 1.14/0.52    inference(superposition,[],[f22,f69])).
% 1.14/0.52  fof(f69,plain,(
% 1.14/0.52    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) | ~spl3_6),
% 1.14/0.52    inference(avatar_component_clause,[],[f68])).
% 1.14/0.52  fof(f68,plain,(
% 1.14/0.52    spl3_6 <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))),
% 1.14/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.14/0.52  fof(f22,plain,(
% 1.14/0.52    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 1.14/0.52    inference(cnf_transformation,[],[f11])).
% 1.14/0.52  fof(f11,plain,(
% 1.14/0.52    ? [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.14/0.52    inference(flattening,[],[f10])).
% 1.14/0.52  fof(f10,plain,(
% 1.14/0.52    ? [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.14/0.52    inference(ennf_transformation,[],[f9])).
% 1.14/0.52  fof(f9,plain,(
% 1.14/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1))))),
% 1.14/0.52    inference(pure_predicate_removal,[],[f8])).
% 1.14/0.52  fof(f8,negated_conjecture,(
% 1.14/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 1.14/0.52    inference(negated_conjecture,[],[f7])).
% 1.14/0.52  fof(f7,conjecture,(
% 1.14/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).
% 1.14/0.52  fof(f74,plain,(
% 1.14/0.52    spl3_5),
% 1.14/0.52    inference(avatar_contradiction_clause,[],[f73])).
% 1.14/0.52  fof(f73,plain,(
% 1.14/0.52    $false | spl3_5),
% 1.14/0.52    inference(resolution,[],[f66,f19])).
% 1.14/0.52  fof(f19,plain,(
% 1.14/0.52    v1_relat_1(sK2)),
% 1.14/0.52    inference(cnf_transformation,[],[f11])).
% 1.14/0.52  fof(f66,plain,(
% 1.14/0.52    ~v1_relat_1(sK2) | spl3_5),
% 1.14/0.52    inference(avatar_component_clause,[],[f65])).
% 1.14/0.52  fof(f65,plain,(
% 1.14/0.52    spl3_5 <=> v1_relat_1(sK2)),
% 1.14/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.14/0.52  fof(f70,plain,(
% 1.14/0.52    ~spl3_5 | spl3_6 | ~spl3_3),
% 1.14/0.52    inference(avatar_split_clause,[],[f63,f56,f68,f65])).
% 1.14/0.52  fof(f56,plain,(
% 1.14/0.52    spl3_3 <=> ! [X0] : (~v5_relat_1(X0,sK0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X0))),
% 1.14/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.14/0.52  fof(f63,plain,(
% 1.14/0.52    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl3_3),
% 1.14/0.52    inference(resolution,[],[f57,f20])).
% 1.14/0.52  fof(f20,plain,(
% 1.14/0.52    v5_relat_1(sK2,sK0)),
% 1.14/0.52    inference(cnf_transformation,[],[f11])).
% 1.14/0.52  fof(f57,plain,(
% 1.14/0.52    ( ! [X0] : (~v5_relat_1(X0,sK0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X0)) ) | ~spl3_3),
% 1.14/0.52    inference(avatar_component_clause,[],[f56])).
% 1.14/0.52  fof(f58,plain,(
% 1.14/0.52    ~spl3_1 | spl3_3),
% 1.14/0.52    inference(avatar_split_clause,[],[f52,f56,f35])).
% 1.14/0.52  fof(f35,plain,(
% 1.14/0.52    spl3_1 <=> v1_relat_1(sK1)),
% 1.14/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.14/0.52  fof(f52,plain,(
% 1.14/0.52    ( ! [X0] : (~v5_relat_1(X0,sK0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(sK1)) )),
% 1.14/0.52    inference(superposition,[],[f47,f50])).
% 1.14/0.52  fof(f50,plain,(
% 1.14/0.52    sK0 = k1_relat_1(sK1)),
% 1.14/0.52    inference(global_subsumption,[],[f23,f24,f49])).
% 1.14/0.52  fof(f49,plain,(
% 1.14/0.52    sK0 = k1_relat_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.14/0.52    inference(forward_demodulation,[],[f48,f45])).
% 1.14/0.52  fof(f45,plain,(
% 1.14/0.52    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.14/0.52    inference(resolution,[],[f32,f25])).
% 1.14/0.52  fof(f25,plain,(
% 1.14/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.14/0.52    inference(cnf_transformation,[],[f11])).
% 1.14/0.52  fof(f32,plain,(
% 1.14/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f18])).
% 1.14/0.52  fof(f18,plain,(
% 1.14/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/0.52    inference(ennf_transformation,[],[f5])).
% 1.14/0.52  fof(f5,axiom,(
% 1.14/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.14/0.52  fof(f48,plain,(
% 1.14/0.52    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.14/0.52    inference(resolution,[],[f31,f25])).
% 1.14/0.52  fof(f31,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 1.14/0.52    inference(cnf_transformation,[],[f17])).
% 1.14/0.52  fof(f17,plain,(
% 1.14/0.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.14/0.52    inference(flattening,[],[f16])).
% 1.14/0.52  fof(f16,plain,(
% 1.14/0.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.14/0.52    inference(ennf_transformation,[],[f6])).
% 1.14/0.52  fof(f6,axiom,(
% 1.14/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.14/0.52  fof(f24,plain,(
% 1.14/0.52    v1_funct_2(sK1,sK0,sK0)),
% 1.14/0.52    inference(cnf_transformation,[],[f11])).
% 1.14/0.52  fof(f23,plain,(
% 1.14/0.52    v1_funct_1(sK1)),
% 1.14/0.52    inference(cnf_transformation,[],[f11])).
% 1.14/0.52  fof(f47,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,k1_relat_1(X0)) | ~v1_relat_1(X1) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 1.14/0.52    inference(duplicate_literal_removal,[],[f46])).
% 1.14/0.52  fof(f46,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v5_relat_1(X1,k1_relat_1(X0))) )),
% 1.14/0.52    inference(resolution,[],[f26,f30])).
% 1.14/0.52  fof(f30,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f15])).
% 1.14/0.52  fof(f15,plain,(
% 1.14/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.14/0.52    inference(ennf_transformation,[],[f2])).
% 1.14/0.52  fof(f2,axiom,(
% 1.14/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.14/0.52  fof(f26,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f13])).
% 1.14/0.52  fof(f13,plain,(
% 1.14/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.14/0.52    inference(flattening,[],[f12])).
% 1.14/0.52  fof(f12,plain,(
% 1.14/0.52    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.14/0.52    inference(ennf_transformation,[],[f4])).
% 1.14/0.52  fof(f4,axiom,(
% 1.14/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.14/0.52  fof(f42,plain,(
% 1.14/0.52    spl3_2),
% 1.14/0.52    inference(avatar_contradiction_clause,[],[f41])).
% 1.14/0.52  fof(f41,plain,(
% 1.14/0.52    $false | spl3_2),
% 1.14/0.52    inference(resolution,[],[f39,f28])).
% 1.14/0.52  fof(f28,plain,(
% 1.14/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.14/0.52    inference(cnf_transformation,[],[f3])).
% 1.14/0.52  fof(f3,axiom,(
% 1.14/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.14/0.52  fof(f39,plain,(
% 1.14/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_2),
% 1.14/0.52    inference(avatar_component_clause,[],[f38])).
% 1.14/0.52  fof(f38,plain,(
% 1.14/0.52    spl3_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.14/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.14/0.52  fof(f40,plain,(
% 1.14/0.52    spl3_1 | ~spl3_2),
% 1.14/0.52    inference(avatar_split_clause,[],[f33,f38,f35])).
% 1.14/0.52  fof(f33,plain,(
% 1.14/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 1.14/0.52    inference(resolution,[],[f27,f25])).
% 1.14/0.52  fof(f27,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f14])).
% 1.14/0.52  fof(f14,plain,(
% 1.14/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.14/0.52    inference(ennf_transformation,[],[f1])).
% 1.14/0.52  fof(f1,axiom,(
% 1.14/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.14/0.52  % SZS output end Proof for theBenchmark
% 1.14/0.52  % (27944)------------------------------
% 1.14/0.52  % (27944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (27944)Termination reason: Refutation
% 1.14/0.52  
% 1.14/0.52  % (27944)Memory used [KB]: 10618
% 1.14/0.52  % (27944)Time elapsed: 0.100 s
% 1.14/0.52  % (27944)------------------------------
% 1.14/0.52  % (27944)------------------------------
% 1.14/0.52  % (27931)Success in time 0.148 s
%------------------------------------------------------------------------------
