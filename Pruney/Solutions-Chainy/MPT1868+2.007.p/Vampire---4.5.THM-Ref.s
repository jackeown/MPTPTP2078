%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 (1864 expanded)
%              Number of leaves         :   19 ( 541 expanded)
%              Depth                    :   61
%              Number of atoms          :  707 (8630 expanded)
%              Number of equality atoms :  113 (1106 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f96,f96,f339])).

fof(f339,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X0,k2_tarski(X1,X1)) ) ),
    inference(resolution,[],[f332,f86])).

% (3292)Refutation not found, incomplete strategy% (3292)------------------------------
% (3292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3292)Termination reason: Refutation not found, incomplete strategy

% (3292)Memory used [KB]: 6268
% (3292)Time elapsed: 0.129 s
% (3292)------------------------------
% (3292)------------------------------
fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (3284)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

% (3293)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

% (3291)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f332,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f331,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

% (3273)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

% (3282)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (3293)Refutation not found, incomplete strategy% (3293)------------------------------
% (3293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3293)Termination reason: Refutation not found, incomplete strategy

% (3293)Memory used [KB]: 6268
% (3293)Time elapsed: 0.137 s
% (3293)------------------------------
% (3293)------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f327,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f325,f56])).

% (3280)Refutation not found, incomplete strategy% (3280)------------------------------
% (3280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3280)Termination reason: Refutation not found, incomplete strategy

% (3280)Memory used [KB]: 10618
% (3280)Time elapsed: 0.139 s
% (3280)------------------------------
% (3280)------------------------------
fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f323,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f323,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) ) ),
    inference(resolution,[],[f320,f114])).

fof(f114,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f80,f109])).

fof(f109,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f107,f59])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f105,f56])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f103,f58])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) ) ),
    inference(resolution,[],[f100,f62])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f87,f64])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f79,f61])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

% (3274)Refutation not found, incomplete strategy% (3274)------------------------------
% (3274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f319,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(k2_tarski(sK1,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(k2_tarski(sK1,sK1)) ) ),
    inference(resolution,[],[f312,f208])).

fof(f208,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f207,f56])).

fof(f207,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f199,f58])).

fof(f199,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f69,f195])).

fof(f195,plain,(
    k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) ),
    inference(resolution,[],[f186,f96])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_tarski(sK1,sK1))
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) ) ),
    inference(resolution,[],[f182,f96])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X0,k2_tarski(X1,X1))
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) ) ),
    inference(resolution,[],[f181,f86])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f180,f58])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f175,f62])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | ~ r2_hidden(X1,X0)
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0)
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f169,f64])).

fof(f169,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X4,X3)
      | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) ) ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,(
    ! [X4,X3] :
      ( k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))
      | k2_tarski(sK1,sK1) != k2_tarski(sK1,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X4,X3)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f162,f114])).

fof(f162,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X1) = k1_tex_2(sK0,sK1)
      | k2_tarski(sK1,sK1) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f158,f85])).

fof(f158,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | sK2(sK0,X0) = k1_tex_2(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tarski(sK1,sK1) != X0 ) ),
    inference(subsumption_resolution,[],[f157,f56])).

fof(f157,plain,(
    ! [X0] :
      ( k2_tarski(sK1,sK1) != X0
      | sK2(sK0,X0) = k1_tex_2(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f58])).

% (3291)Refutation not found, incomplete strategy% (3291)------------------------------
% (3291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3291)Termination reason: Refutation not found, incomplete strategy

% (3291)Memory used [KB]: 6268
% (3291)Time elapsed: 0.139 s
% (3291)------------------------------
% (3291)------------------------------
fof(f156,plain,(
    ! [X0] :
      ( k2_tarski(sK1,sK1) != X0
      | sK2(sK0,X0) = k1_tex_2(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

% (3294)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f155,plain,(
    ! [X0] :
      ( k2_tarski(sK1,sK1) != X0
      | sK2(sK0,X0) = k1_tex_2(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f154,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

% (3283)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f154,plain,(
    ! [X0] :
      ( k2_tarski(sK1,sK1) != u1_struct_0(sK2(sK0,X0))
      | sK2(sK0,X0) = k1_tex_2(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f153,f109])).

fof(f153,plain,(
    ! [X0] :
      ( sK2(sK0,X0) = k1_tex_2(sK0,sK1)
      | k6_domain_1(u1_struct_0(sK0),sK1) != u1_struct_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f152,f59])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK2(sK0,X0) = k1_tex_2(sK0,X1)
      | k6_domain_1(u1_struct_0(sK0),X1) != u1_struct_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f150,f56])).

fof(f150,plain,(
    ! [X0,X1] :
      ( sK2(sK0,X0) = k1_tex_2(sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k6_domain_1(u1_struct_0(sK0),X1) != u1_struct_0(sK2(sK0,X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f146,f58])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | sK2(X0,X1) = k1_tex_2(X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X0),X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X0),X2)
      | sK2(X0,X1) = k1_tex_2(X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f116,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(sK2(X0,X1),X2)
      | u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X2),X3)
      | sK2(X0,X1) = k1_tex_2(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f115,f69])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X2),X3)
      | ~ m1_pre_topc(sK2(X0,X1),X2)
      | sK2(X0,X1) = k1_tex_2(X2,X3)
      | v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f68,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(X2)
      | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(X2,X0)
      | k1_tex_2(X0,X1) = X2
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f312,plain,(
    ! [X0,X1] :
      ( v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f311,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f310,f58])).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f308,f228])).

fof(f228,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f212,f85])).

fof(f212,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f211,f56])).

fof(f211,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f58])).

% (3276)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (3281)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (3275)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (3274)Termination reason: Refutation not found, incomplete strategy

% (3274)Memory used [KB]: 10746
% (3274)Time elapsed: 0.145 s
% (3274)------------------------------
% (3274)------------------------------
% (3285)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (3295)Refutation not found, incomplete strategy% (3295)------------------------------
% (3295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3295)Termination reason: Refutation not found, incomplete strategy

% (3295)Memory used [KB]: 1663
% (3295)Time elapsed: 0.133 s
% (3295)------------------------------
% (3295)------------------------------
fof(f201,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f71,f195])).

fof(f308,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f212,f289,f307])).

% (3281)Refutation not found, incomplete strategy% (3281)------------------------------
% (3281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3281)Termination reason: Refutation not found, incomplete strategy

% (3281)Memory used [KB]: 1791
% (3281)Time elapsed: 0.146 s
% (3281)------------------------------
% (3281)------------------------------
% (3289)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (3276)Refutation not found, incomplete strategy% (3276)------------------------------
% (3276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3276)Termination reason: Refutation not found, incomplete strategy

% (3276)Memory used [KB]: 10618
% (3276)Time elapsed: 0.004 s
% (3276)------------------------------
% (3276)------------------------------
fof(f307,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f306,f56])).

fof(f306,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f305,f58])).

fof(f305,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f299,f110])).

fof(f110,plain,(
    ~ v2_tex_2(k2_tarski(sK1,sK1),sK0) ),
    inference(backward_demodulation,[],[f60,f109])).

fof(f60,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f299,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k2_tarski(sK1,sK1),X0)
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f286,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f286,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k2_tarski(sK1,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f285,f56])).

fof(f285,plain,(
    ! [X0] :
      ( v2_tex_2(k2_tarski(sK1,sK1),X0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f284,f58])).

fof(f284,plain,(
    ! [X0] :
      ( v2_tex_2(k2_tarski(sK1,sK1),X0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f59])).

fof(f279,plain,(
    ! [X0] :
      ( v2_tex_2(k2_tarski(sK1,sK1),X0)
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f108,f266])).

fof(f266,plain,(
    k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f263,f96])).

fof(f263,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_tarski(sK1,sK1))
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(resolution,[],[f259,f96])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X0,k2_tarski(X1,X1))
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(resolution,[],[f256,f86])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f255,f58])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f254,f62])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | ~ r2_hidden(X1,X0)
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f252,f56])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0)
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f248,f64])).

fof(f248,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0)
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(resolution,[],[f232,f114])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f214,f85])).

fof(f214,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f213,f56])).

fof(f213,plain,
    ( k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f58])).

fof(f202,plain,
    ( k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f72,f195])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(u1_struct_0(k1_tex_2(X0,X1)),X2)
      | ~ m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X2)
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ v2_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(k1_tex_2(X0,X1))
            & v1_tdlat_3(k1_tex_2(X0,X1)) )
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(k1_tex_2(X0,X1))
            & v1_tdlat_3(k1_tex_2(X0,X1)) )
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f289,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
      | ~ v1_xboole_0(k2_tarski(sK1,sK1))
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f288,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f288,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(k2_tarski(sK1,sK1)) ),
    inference(resolution,[],[f282,f62])).

fof(f282,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(k2_tarski(sK1,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(superposition,[],[f64,f266])).

fof(f96,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f82,f61])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (3287)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (3278)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (3267)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3263)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (3271)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (3278)Refutation not found, incomplete strategy% (3278)------------------------------
% 0.21/0.51  % (3278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3278)Memory used [KB]: 1791
% 0.21/0.51  % (3278)Time elapsed: 0.054 s
% 0.21/0.51  % (3278)------------------------------
% 0.21/0.51  % (3278)------------------------------
% 0.21/0.51  % (3279)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (3269)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (3277)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (3272)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (3266)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (3274)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (3268)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (3265)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (3290)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (3264)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (3264)Refutation not found, incomplete strategy% (3264)------------------------------
% 0.21/0.54  % (3264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3264)Memory used [KB]: 1663
% 0.21/0.54  % (3264)Time elapsed: 0.125 s
% 0.21/0.54  % (3264)------------------------------
% 0.21/0.54  % (3264)------------------------------
% 0.21/0.54  % (3295)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3292)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3280)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (3287)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f96,f96,f339])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k2_tarski(sK1,sK1)) | ~r2_hidden(X0,k2_tarski(X1,X1))) )),
% 0.21/0.54    inference(resolution,[],[f332,f86])).
% 0.21/0.54  % (3292)Refutation not found, incomplete strategy% (3292)------------------------------
% 0.21/0.54  % (3292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3292)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3292)Memory used [KB]: 6268
% 0.21/0.54  % (3292)Time elapsed: 0.129 s
% 0.21/0.54  % (3292)------------------------------
% 0.21/0.54  % (3292)------------------------------
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f77,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  % (3284)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  % (3293)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.54  % (3291)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  fof(f332,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f331,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f46,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (3273)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  % (3282)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (3293)Refutation not found, incomplete strategy% (3293)------------------------------
% 0.21/0.54  % (3293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3293)Memory used [KB]: 6268
% 0.21/0.54  % (3293)Time elapsed: 0.137 s
% 0.21/0.54  % (3293)------------------------------
% 0.21/0.54  % (3293)------------------------------
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f327,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f325,f56])).
% 0.21/0.54  % (3280)Refutation not found, incomplete strategy% (3280)------------------------------
% 0.21/0.54  % (3280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3280)Memory used [KB]: 10618
% 0.21/0.54  % (3280)Time elapsed: 0.139 s
% 0.21/0.54  % (3280)------------------------------
% 0.21/0.54  % (3280)------------------------------
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f323,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))) )),
% 0.21/0.54    inference(resolution,[],[f320,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f113,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.54    inference(superposition,[],[f80,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.54    inference(resolution,[],[f107,f59])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f105,f56])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) )),
% 0.21/0.54    inference(resolution,[],[f103,f58])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0)) )),
% 0.21/0.54    inference(resolution,[],[f100,f62])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_struct_0(X1) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(resolution,[],[f87,f64])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f79,f61])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  % (3274)Refutation not found, incomplete strategy% (3274)------------------------------
% 0.21/0.54  % (3274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f319,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0) | v1_xboole_0(k2_tarski(sK1,sK1))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f317])).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1))) )),
% 0.21/0.54    inference(resolution,[],[f312,f208])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f207,f56])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1)) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f199,f58])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(superposition,[],[f69,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))),
% 0.21/0.54    inference(resolution,[],[f186,f96])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK1,sK1)) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))) )),
% 0.21/0.54    inference(resolution,[],[f182,f96])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k2_tarski(sK1,sK1)) | ~r2_hidden(X0,k2_tarski(X1,X1)) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))) )),
% 0.21/0.54    inference(resolution,[],[f181,f86])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1))) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f180,f58])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f175,f62])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_struct_0(sK0) | ~r2_hidden(X1,X0) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f173,f56])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f169,f64])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X4,X3] : (v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X4,X3) | k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1))) )),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k1_tex_2(sK0,sK1) = sK2(sK0,k2_tarski(sK1,sK1)) | k2_tarski(sK1,sK1) != k2_tarski(sK1,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X4,X3) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f162,f114])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X1) = k1_tex_2(sK0,sK1) | k2_tarski(sK1,sK1) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(X3,X2)) )),
% 0.21/0.54    inference(resolution,[],[f158,f85])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(X0) | sK2(sK0,X0) = k1_tex_2(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(sK1,sK1) != X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f157,f56])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(sK1,sK1) != X0 | sK2(sK0,X0) = k1_tex_2(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f156,f58])).
% 0.21/0.54  % (3291)Refutation not found, incomplete strategy% (3291)------------------------------
% 0.21/0.54  % (3291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3291)Memory used [KB]: 6268
% 0.21/0.54  % (3291)Time elapsed: 0.139 s
% 0.21/0.54  % (3291)------------------------------
% 0.21/0.54  % (3291)------------------------------
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(sK1,sK1) != X0 | sK2(sK0,X0) = k1_tex_2(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f155])).
% 0.21/0.54  % (3294)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(sK1,sK1) != X0 | sK2(sK0,X0) = k1_tex_2(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(superposition,[],[f154,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (3283)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(sK1,sK1) != u1_struct_0(sK2(sK0,X0)) | sK2(sK0,X0) = k1_tex_2(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f153,f109])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_tex_2(sK0,sK1) | k6_domain_1(u1_struct_0(sK0),sK1) != u1_struct_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f152,f59])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0,X0) = k1_tex_2(sK0,X1) | k6_domain_1(u1_struct_0(sK0),X1) != u1_struct_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f56])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK2(sK0,X0) = k1_tex_2(sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X1) != u1_struct_0(sK2(sK0,X0)) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f146,f58])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | sK2(X0,X1) = k1_tex_2(X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X0),X2) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X0),X2) | sK2(X0,X1) = k1_tex_2(X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f116,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(sK2(X0,X1),X2) | u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X2),X3) | sK2(X0,X1) = k1_tex_2(X2,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f69])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (u1_struct_0(sK2(X0,X1)) != k6_domain_1(u1_struct_0(X2),X3) | ~m1_pre_topc(sK2(X0,X1),X2) | sK2(X0,X1) = k1_tex_2(X2,X3) | v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f68,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_pre_topc(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_pre_topc(X2) | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(X2,X0) | k1_tex_2(X0,X1) = X2 | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f311,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f310,f58])).
% 0.21/0.54  fof(f310,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f309])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f308,f228])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f212,f85])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    v1_xboole_0(k2_tarski(sK1,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f211,f56])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1)) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f201,f58])).
% 0.21/0.55  % (3276)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (3281)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (3275)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (3274)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3274)Memory used [KB]: 10746
% 0.21/0.55  % (3274)Time elapsed: 0.145 s
% 0.21/0.55  % (3274)------------------------------
% 0.21/0.55  % (3274)------------------------------
% 0.21/0.55  % (3285)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (3295)Refutation not found, incomplete strategy% (3295)------------------------------
% 0.21/0.55  % (3295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3295)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3295)Memory used [KB]: 1663
% 0.21/0.55  % (3295)Time elapsed: 0.133 s
% 0.21/0.55  % (3295)------------------------------
% 0.21/0.55  % (3295)------------------------------
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.55    inference(superposition,[],[f71,f195])).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(global_subsumption,[],[f212,f289,f307])).
% 0.21/0.55  % (3281)Refutation not found, incomplete strategy% (3281)------------------------------
% 0.21/0.55  % (3281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3281)Memory used [KB]: 1791
% 0.21/0.56  % (3281)Time elapsed: 0.146 s
% 0.21/0.56  % (3281)------------------------------
% 0.21/0.56  % (3281)------------------------------
% 0.21/0.56  % (3289)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (3276)Refutation not found, incomplete strategy% (3276)------------------------------
% 0.21/0.56  % (3276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3276)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3276)Memory used [KB]: 10618
% 0.21/0.56  % (3276)Time elapsed: 0.004 s
% 0.21/0.56  % (3276)------------------------------
% 0.21/0.56  % (3276)------------------------------
% 0.21/0.56  fof(f307,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f306,f56])).
% 0.21/0.56  fof(f306,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f305,f58])).
% 0.21/0.56  fof(f305,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.56    inference(resolution,[],[f299,f110])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ~v2_tex_2(k2_tarski(sK1,sK1),sK0)),
% 0.21/0.56    inference(backward_demodulation,[],[f60,f109])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f47])).
% 0.21/0.56  fof(f299,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_tex_2(k2_tarski(sK1,sK1),X0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.56    inference(resolution,[],[f286,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_pre_topc(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k2_tarski(sK1,sK1),X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f285,f56])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    ( ! [X0] : (v2_tex_2(k2_tarski(sK1,sK1),X0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f284,f58])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    ( ! [X0] : (v2_tex_2(k2_tarski(sK1,sK1),X0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f279,f59])).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    ( ! [X0] : (v2_tex_2(k2_tarski(sK1,sK1),X0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.56    inference(superposition,[],[f108,f266])).
% 0.21/0.56  fof(f266,plain,(
% 0.21/0.56    k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.56    inference(resolution,[],[f263,f96])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK1,sK1)) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.56    inference(resolution,[],[f259,f96])).
% 0.21/0.56  fof(f259,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k2_tarski(sK1,sK1)) | ~r2_hidden(X0,k2_tarski(X1,X1)) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.56    inference(resolution,[],[f256,f86])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1))) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f255,f58])).
% 0.21/0.56  fof(f255,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.56    inference(resolution,[],[f254,f62])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_struct_0(sK0) | ~r2_hidden(X1,X0) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1)))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f252,f56])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.56    inference(resolution,[],[f248,f64])).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.56    inference(resolution,[],[f232,f114])).
% 0.21/0.56  fof(f232,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f214,f85])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    v1_xboole_0(k2_tarski(sK1,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f213,f56])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1)) | v2_struct_0(sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f202,f58])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    k2_tarski(sK1,sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_tarski(sK1,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.56    inference(superposition,[],[f72,f195])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_tex_2(u1_struct_0(k1_tex_2(X0,X1)),X2) | ~m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(k1_tex_2(X0,X1),X2) | v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(resolution,[],[f93,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (((v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))) | ~v2_pre_topc(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.56  fof(f289,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~v1_xboole_0(k2_tarski(sK1,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(resolution,[],[f288,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.56  fof(f288,plain,(
% 0.21/0.56    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(k2_tarski(sK1,sK1))),
% 0.21/0.56    inference(resolution,[],[f282,f62])).
% 0.21/0.56  fof(f282,plain,(
% 0.21/0.56    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(k2_tarski(sK1,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f64,f266])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.21/0.56    inference(equality_resolution,[],[f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.21/0.56    inference(equality_resolution,[],[f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.21/0.56    inference(definition_unfolding,[],[f82,f61])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(rectify,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (3287)------------------------------
% 0.21/0.56  % (3287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3287)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (3287)Memory used [KB]: 6652
% 0.21/0.56  % (3287)Time elapsed: 0.084 s
% 0.21/0.56  % (3287)------------------------------
% 0.21/0.56  % (3287)------------------------------
% 0.21/0.57  % (3260)Success in time 0.201 s
%------------------------------------------------------------------------------
