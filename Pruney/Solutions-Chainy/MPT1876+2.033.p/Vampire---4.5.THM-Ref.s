%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:41 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 975 expanded)
%              Number of leaves         :   37 ( 286 expanded)
%              Depth                    :   20
%              Number of atoms          :  857 (7444 expanded)
%              Number of equality atoms :   78 ( 178 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f124,f226,f235,f244,f253,f262,f270,f278,f405,f409,f420,f444,f497,f525,f531])).

fof(f531,plain,
    ( spl6_1
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | spl6_1
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f528,f455])).

fof(f455,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f446,f448])).

fof(f448,plain,
    ( k1_xboole_0 = sK2(sK0,sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f221,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f221,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl6_12
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f446,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f269,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f269,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl6_18
  <=> r1_tarski(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f528,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | spl6_1
    | ~ spl6_12
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f453,f492])).

fof(f492,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl6_38
  <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f453,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),sK1)
    | spl6_1
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f426,f448])).

fof(f426,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f425,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f425,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f424,f74])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f424,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f423,f76])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f423,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f422,f78])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f422,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f421,f118])).

fof(f118,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f421,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f97,f166])).

fof(f166,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),sK1,X1) = k3_xboole_0(X1,sK1) ),
    inference(backward_demodulation,[],[f138,f139])).

fof(f139,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK1) = k3_xboole_0(X2,sK1) ),
    inference(resolution,[],[f78,f113])).

% (23635)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (23623)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (23621)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (23621)Refutation not found, incomplete strategy% (23621)------------------------------
% (23621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23621)Termination reason: Refutation not found, incomplete strategy

% (23621)Memory used [KB]: 10746
% (23621)Time elapsed: 0.153 s
% (23621)------------------------------
% (23621)------------------------------
% (23636)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f138,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f78,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f525,plain,
    ( ~ spl6_12
    | ~ spl6_19
    | spl6_39 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_19
    | spl6_39 ),
    inference(subsumption_resolution,[],[f496,f522])).

fof(f522,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f521,f74])).

fof(f521,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f520,f76])).

fof(f520,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f470,f81])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f470,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(resolution,[],[f452,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f452,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f277,f448])).

fof(f277,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_19
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f496,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl6_39 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl6_39
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f497,plain,
    ( spl6_38
    | ~ spl6_39
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f488,f275,f219,f494,f490])).

fof(f488,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f461,f76])).

fof(f461,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(resolution,[],[f452,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f444,plain,
    ( spl6_1
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f440,f197])).

fof(f197,plain,(
    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f141,f107])).

fof(f141,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f127,f76])).

fof(f127,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f440,plain,
    ( sK1 != k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | spl6_1
    | ~ spl6_13 ),
    inference(superposition,[],[f427,f106])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f427,plain,
    ( sK1 != k3_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl6_1
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f426,f225])).

fof(f225,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_13
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f420,plain,
    ( ~ spl6_15
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl6_15
    | spl6_34 ),
    inference(subsumption_resolution,[],[f418,f307])).

fof(f307,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f297,f76])).

fof(f297,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f243,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f243,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_15
  <=> m1_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f418,plain,
    ( ~ l1_pre_topc(sK3(sK0,sK1))
    | spl6_34 ),
    inference(resolution,[],[f404,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f404,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl6_34
  <=> l1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f409,plain,
    ( spl6_17
    | spl6_21
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f408,f250,f241,f287,f259])).

fof(f259,plain,
    ( spl6_17
  <=> v2_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f287,plain,
    ( spl6_21
  <=> v7_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f250,plain,
    ( spl6_16
  <=> v1_tdlat_3(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f408,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | v2_struct_0(sK3(sK0,sK1))
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f407,f307])).

fof(f407,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f406,f397])).

fof(f397,plain,
    ( v2_pre_topc(sK3(sK0,sK1))
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f393,f307])).

fof(f393,plain,
    ( v2_pre_topc(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_15 ),
    inference(resolution,[],[f311,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f311,plain,
    ( v2_tdlat_3(sK3(sK0,sK1))
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f310,f73])).

fof(f310,plain,
    ( v2_tdlat_3(sK3(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f309,f74])).

fof(f309,plain,
    ( v2_tdlat_3(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f308,f75])).

fof(f75,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f308,plain,
    ( v2_tdlat_3(sK3(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f296,f76])).

fof(f296,plain,
    ( v2_tdlat_3(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f243,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f406,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK3(sK0,sK1))
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f279,f311])).

fof(f279,plain,
    ( ~ v2_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK3(sK0,sK1))
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_16 ),
    inference(resolution,[],[f252,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f252,plain,
    ( v1_tdlat_3(sK3(sK0,sK1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f250])).

fof(f405,plain,
    ( ~ spl6_21
    | ~ spl6_34
    | spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f325,f232,f120,f402,f287])).

fof(f120,plain,
    ( spl6_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f232,plain,
    ( spl6_14
  <=> sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f325,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK3(sK0,sK1))
    | ~ v7_struct_0(sK3(sK0,sK1))
    | ~ spl6_14 ),
    inference(superposition,[],[f102,f234])).

fof(f234,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f232])).

fof(f102,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f278,plain,
    ( spl6_1
    | spl6_19 ),
    inference(avatar_split_clause,[],[f273,f275,f116])).

fof(f273,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f272,f73])).

fof(f272,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f271,f74])).

fof(f271,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f76])).

fof(f131,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f270,plain,
    ( spl6_1
    | spl6_18 ),
    inference(avatar_split_clause,[],[f265,f267,f116])).

fof(f265,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f264,f73])).

fof(f264,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f74])).

fof(f263,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f76])).

fof(f132,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f262,plain,
    ( ~ spl6_17
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f257,f116,f259])).

fof(f257,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f256,f73])).

fof(f256,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f74])).

fof(f255,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f76])).

fof(f254,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f77])).

fof(f77,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK3(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & v1_tdlat_3(sK3(X0,X1))
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & v1_tdlat_3(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f253,plain,
    ( spl6_16
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f248,f116,f250])).

fof(f248,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f247,f73])).

fof(f247,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f246,f74])).

fof(f246,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f245,f76])).

fof(f245,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f77])).

fof(f134,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK3(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f244,plain,
    ( spl6_15
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f239,f116,f241])).

fof(f239,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f238,f73])).

fof(f238,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f237,f74])).

fof(f237,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f76])).

fof(f236,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f77])).

fof(f135,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK3(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f235,plain,
    ( spl6_14
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f230,f116,f232])).

fof(f230,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f229,f73])).

fof(f229,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f74])).

fof(f228,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f227,f76])).

fof(f227,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f77])).

fof(f136,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK3(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f226,plain,
    ( spl6_12
    | spl6_13
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f217,f120,f116,f223,f219])).

fof(f217,plain,
    ( sK1 = sK2(sK0,sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f216,f77])).

fof(f216,plain,
    ( sK1 = sK2(sK0,sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f215,f121])).

fof(f121,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f215,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f165,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f165,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f164,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f163,f74])).

fof(f163,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f162,f76])).

fof(f162,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f132,f118])).

fof(f124,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f79,f120,f116])).

fof(f79,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f123,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f80,f120,f116])).

fof(f80,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:22:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (23617)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (23625)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (23633)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (23633)Refutation not found, incomplete strategy% (23633)------------------------------
% 0.20/0.50  % (23633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23616)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (23611)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (23633)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23633)Memory used [KB]: 10874
% 0.20/0.51  % (23633)Time elapsed: 0.106 s
% 0.20/0.51  % (23633)------------------------------
% 0.20/0.51  % (23633)------------------------------
% 0.20/0.51  % (23626)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.52  % (23622)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.52  % (23624)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.52  % (23614)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.52  % (23615)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.52  % (23613)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.52  % (23640)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.52  % (23618)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.53  % (23632)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (23627)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.53  % (23620)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.53  % (23634)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.53  % (23638)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.53  % (23639)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.53  % (23637)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.53  % (23619)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.54  % (23630)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.54  % (23628)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (23631)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (23629)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (23612)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.54  % (23619)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f532,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f123,f124,f226,f235,f244,f253,f262,f270,f278,f405,f409,f420,f444,f497,f525,f531])).
% 1.32/0.54  fof(f531,plain,(
% 1.32/0.54    spl6_1 | ~spl6_12 | ~spl6_18 | ~spl6_38),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f530])).
% 1.32/0.54  fof(f530,plain,(
% 1.32/0.54    $false | (spl6_1 | ~spl6_12 | ~spl6_18 | ~spl6_38)),
% 1.32/0.54    inference(subsumption_resolution,[],[f528,f455])).
% 1.32/0.54  fof(f455,plain,(
% 1.32/0.54    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | (~spl6_12 | ~spl6_18)),
% 1.32/0.54    inference(backward_demodulation,[],[f446,f448])).
% 1.32/0.54  fof(f448,plain,(
% 1.32/0.54    k1_xboole_0 = sK2(sK0,sK1) | ~spl6_12),
% 1.32/0.54    inference(resolution,[],[f221,f92])).
% 1.32/0.54  fof(f92,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.32/0.54  fof(f221,plain,(
% 1.32/0.54    v1_xboole_0(sK2(sK0,sK1)) | ~spl6_12),
% 1.32/0.54    inference(avatar_component_clause,[],[f219])).
% 1.32/0.54  fof(f219,plain,(
% 1.32/0.54    spl6_12 <=> v1_xboole_0(sK2(sK0,sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.32/0.54  fof(f446,plain,(
% 1.32/0.54    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),sK1) | ~spl6_18),
% 1.32/0.54    inference(resolution,[],[f269,f107])).
% 1.32/0.54  fof(f107,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f49])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.32/0.54  fof(f269,plain,(
% 1.32/0.54    r1_tarski(sK2(sK0,sK1),sK1) | ~spl6_18),
% 1.32/0.54    inference(avatar_component_clause,[],[f267])).
% 1.32/0.54  fof(f267,plain,(
% 1.32/0.54    spl6_18 <=> r1_tarski(sK2(sK0,sK1),sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.32/0.54  fof(f528,plain,(
% 1.32/0.54    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | (spl6_1 | ~spl6_12 | ~spl6_38)),
% 1.32/0.54    inference(backward_demodulation,[],[f453,f492])).
% 1.32/0.54  fof(f492,plain,(
% 1.32/0.54    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl6_38),
% 1.32/0.54    inference(avatar_component_clause,[],[f490])).
% 1.32/0.54  fof(f490,plain,(
% 1.32/0.54    spl6_38 <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.32/0.54  fof(f453,plain,(
% 1.32/0.54    k1_xboole_0 != k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),sK1) | (spl6_1 | ~spl6_12)),
% 1.32/0.54    inference(backward_demodulation,[],[f426,f448])).
% 1.32/0.54  fof(f426,plain,(
% 1.32/0.54    sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1) | spl6_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f425,f73])).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ~v2_struct_0(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f57])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f53])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,negated_conjecture,(
% 1.32/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.32/0.54    inference(negated_conjecture,[],[f22])).
% 1.32/0.54  fof(f22,conjecture,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.32/0.54  fof(f425,plain,(
% 1.32/0.54    sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f424,f74])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    v2_pre_topc(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f57])).
% 1.32/0.54  fof(f424,plain,(
% 1.32/0.54    sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f423,f76])).
% 1.32/0.54  fof(f76,plain,(
% 1.32/0.54    l1_pre_topc(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f57])).
% 1.32/0.54  fof(f423,plain,(
% 1.32/0.54    sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f422,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    inference(cnf_transformation,[],[f57])).
% 1.32/0.54  fof(f422,plain,(
% 1.32/0.54    sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f421,f118])).
% 1.32/0.54  fof(f118,plain,(
% 1.32/0.54    ~v2_tex_2(sK1,sK0) | spl6_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f116])).
% 1.32/0.54  fof(f116,plain,(
% 1.32/0.54    spl6_1 <=> v2_tex_2(sK1,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.32/0.54  fof(f421,plain,(
% 1.32/0.54    sK2(sK0,sK1) != k3_xboole_0(k2_pre_topc(sK0,sK2(sK0,sK1)),sK1) | v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.54    inference(superposition,[],[f97,f166])).
% 1.32/0.54  fof(f166,plain,(
% 1.32/0.54    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),sK1,X1) = k3_xboole_0(X1,sK1)) )),
% 1.32/0.54    inference(backward_demodulation,[],[f138,f139])).
% 1.32/0.54  fof(f139,plain,(
% 1.32/0.54    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,sK1) = k3_xboole_0(X2,sK1)) )),
% 1.32/0.54    inference(resolution,[],[f78,f113])).
% 1.32/0.54  % (23635)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (23623)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (23621)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.55  % (23621)Refutation not found, incomplete strategy% (23621)------------------------------
% 1.32/0.55  % (23621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (23621)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (23621)Memory used [KB]: 10746
% 1.32/0.55  % (23621)Time elapsed: 0.153 s
% 1.32/0.55  % (23621)------------------------------
% 1.32/0.55  % (23621)------------------------------
% 1.32/0.55  % (23636)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.56  fof(f113,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f51])).
% 1.32/0.56  fof(f51,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f8])).
% 1.32/0.56  fof(f8,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.32/0.56  fof(f138,plain,(
% 1.32/0.56    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 1.32/0.56    inference(resolution,[],[f78,f114])).
% 1.32/0.56  fof(f114,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f52])).
% 1.32/0.56  fof(f52,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f7])).
% 1.32/0.56  fof(f7,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.32/0.56  fof(f97,plain,(
% 1.32/0.56    ( ! [X0,X1] : (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f61])).
% 1.32/0.56  fof(f61,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f59,f60])).
% 1.32/0.56  fof(f60,plain,(
% 1.32/0.56    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f59,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(rectify,[],[f58])).
% 1.32/0.56  fof(f58,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(nnf_transformation,[],[f42])).
% 1.32/0.56  fof(f42,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(flattening,[],[f41])).
% 1.32/0.56  fof(f41,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f21])).
% 1.32/0.56  fof(f21,axiom,(
% 1.32/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 1.32/0.56  fof(f525,plain,(
% 1.32/0.56    ~spl6_12 | ~spl6_19 | spl6_39),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f524])).
% 1.32/0.56  fof(f524,plain,(
% 1.32/0.56    $false | (~spl6_12 | ~spl6_19 | spl6_39)),
% 1.32/0.56    inference(subsumption_resolution,[],[f496,f522])).
% 1.32/0.56  fof(f522,plain,(
% 1.32/0.56    v4_pre_topc(k1_xboole_0,sK0) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(subsumption_resolution,[],[f521,f74])).
% 1.32/0.56  fof(f521,plain,(
% 1.32/0.56    v4_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(subsumption_resolution,[],[f520,f76])).
% 1.32/0.56  fof(f520,plain,(
% 1.32/0.56    v4_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(subsumption_resolution,[],[f470,f81])).
% 1.32/0.56  fof(f81,plain,(
% 1.32/0.56    v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    inference(cnf_transformation,[],[f4])).
% 1.32/0.56  fof(f4,axiom,(
% 1.32/0.56    v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.32/0.56  fof(f470,plain,(
% 1.32/0.56    ~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(resolution,[],[f452,f103])).
% 1.32/0.56  fof(f103,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f48])).
% 1.32/0.56  fof(f48,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.56    inference(flattening,[],[f47])).
% 1.32/0.56  fof(f47,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f10])).
% 1.32/0.56  fof(f10,axiom,(
% 1.32/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.32/0.56  fof(f452,plain,(
% 1.32/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(backward_demodulation,[],[f277,f448])).
% 1.32/0.56  fof(f277,plain,(
% 1.32/0.56    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_19),
% 1.32/0.56    inference(avatar_component_clause,[],[f275])).
% 1.32/0.56  fof(f275,plain,(
% 1.32/0.56    spl6_19 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.32/0.56  fof(f496,plain,(
% 1.32/0.56    ~v4_pre_topc(k1_xboole_0,sK0) | spl6_39),
% 1.32/0.56    inference(avatar_component_clause,[],[f494])).
% 1.32/0.56  fof(f494,plain,(
% 1.32/0.56    spl6_39 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.32/0.56  fof(f497,plain,(
% 1.32/0.56    spl6_38 | ~spl6_39 | ~spl6_12 | ~spl6_19),
% 1.32/0.56    inference(avatar_split_clause,[],[f488,f275,f219,f494,f490])).
% 1.32/0.56  fof(f488,plain,(
% 1.32/0.56    ~v4_pre_topc(k1_xboole_0,sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(subsumption_resolution,[],[f461,f76])).
% 1.32/0.56  fof(f461,plain,(
% 1.32/0.56    ~v4_pre_topc(k1_xboole_0,sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl6_12 | ~spl6_19)),
% 1.32/0.56    inference(resolution,[],[f452,f90])).
% 1.32/0.56  fof(f90,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f37])).
% 1.32/0.56  fof(f37,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(flattening,[],[f36])).
% 1.32/0.56  fof(f36,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f15])).
% 1.32/0.56  fof(f15,axiom,(
% 1.32/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.32/0.56  fof(f444,plain,(
% 1.32/0.56    spl6_1 | ~spl6_13),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f443])).
% 1.32/0.56  fof(f443,plain,(
% 1.32/0.56    $false | (spl6_1 | ~spl6_13)),
% 1.32/0.56    inference(subsumption_resolution,[],[f440,f197])).
% 1.32/0.56  fof(f197,plain,(
% 1.32/0.56    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 1.32/0.56    inference(resolution,[],[f141,f107])).
% 1.32/0.56  fof(f141,plain,(
% 1.32/0.56    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.32/0.56    inference(subsumption_resolution,[],[f127,f76])).
% 1.32/0.56  fof(f127,plain,(
% 1.32/0.56    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f89])).
% 1.32/0.56  fof(f89,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f35])).
% 1.32/0.56  fof(f35,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f14])).
% 1.32/0.56  fof(f14,axiom,(
% 1.32/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.32/0.56  fof(f440,plain,(
% 1.32/0.56    sK1 != k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (spl6_1 | ~spl6_13)),
% 1.32/0.56    inference(superposition,[],[f427,f106])).
% 1.32/0.56  fof(f106,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  fof(f1,axiom,(
% 1.32/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.32/0.56  fof(f427,plain,(
% 1.32/0.56    sK1 != k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl6_1 | ~spl6_13)),
% 1.32/0.56    inference(forward_demodulation,[],[f426,f225])).
% 1.32/0.56  fof(f225,plain,(
% 1.32/0.56    sK1 = sK2(sK0,sK1) | ~spl6_13),
% 1.32/0.56    inference(avatar_component_clause,[],[f223])).
% 1.32/0.56  fof(f223,plain,(
% 1.32/0.56    spl6_13 <=> sK1 = sK2(sK0,sK1)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.32/0.56  fof(f420,plain,(
% 1.32/0.56    ~spl6_15 | spl6_34),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f419])).
% 1.32/0.56  fof(f419,plain,(
% 1.32/0.56    $false | (~spl6_15 | spl6_34)),
% 1.32/0.56    inference(subsumption_resolution,[],[f418,f307])).
% 1.32/0.56  fof(f307,plain,(
% 1.32/0.56    l1_pre_topc(sK3(sK0,sK1)) | ~spl6_15),
% 1.32/0.56    inference(subsumption_resolution,[],[f297,f76])).
% 1.32/0.56  fof(f297,plain,(
% 1.32/0.56    l1_pre_topc(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl6_15),
% 1.32/0.56    inference(resolution,[],[f243,f88])).
% 1.32/0.56  fof(f88,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f34])).
% 1.32/0.56  fof(f34,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f12])).
% 1.32/0.56  fof(f12,axiom,(
% 1.32/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.32/0.56  fof(f243,plain,(
% 1.32/0.56    m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl6_15),
% 1.32/0.56    inference(avatar_component_clause,[],[f241])).
% 1.32/0.56  fof(f241,plain,(
% 1.32/0.56    spl6_15 <=> m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.32/0.56  fof(f418,plain,(
% 1.32/0.56    ~l1_pre_topc(sK3(sK0,sK1)) | spl6_34),
% 1.32/0.56    inference(resolution,[],[f404,f83])).
% 1.32/0.56  fof(f83,plain,(
% 1.32/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f29])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f11])).
% 1.32/0.56  fof(f11,axiom,(
% 1.32/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.32/0.56  fof(f404,plain,(
% 1.32/0.56    ~l1_struct_0(sK3(sK0,sK1)) | spl6_34),
% 1.32/0.56    inference(avatar_component_clause,[],[f402])).
% 1.32/0.56  fof(f402,plain,(
% 1.32/0.56    spl6_34 <=> l1_struct_0(sK3(sK0,sK1))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.32/0.56  fof(f409,plain,(
% 1.32/0.56    spl6_17 | spl6_21 | ~spl6_15 | ~spl6_16),
% 1.32/0.56    inference(avatar_split_clause,[],[f408,f250,f241,f287,f259])).
% 1.32/0.56  fof(f259,plain,(
% 1.32/0.56    spl6_17 <=> v2_struct_0(sK3(sK0,sK1))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.32/0.56  fof(f287,plain,(
% 1.32/0.56    spl6_21 <=> v7_struct_0(sK3(sK0,sK1))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.32/0.56  fof(f250,plain,(
% 1.32/0.56    spl6_16 <=> v1_tdlat_3(sK3(sK0,sK1))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.32/0.56  fof(f408,plain,(
% 1.32/0.56    v7_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK3(sK0,sK1)) | (~spl6_15 | ~spl6_16)),
% 1.32/0.56    inference(subsumption_resolution,[],[f407,f307])).
% 1.32/0.56  fof(f407,plain,(
% 1.32/0.56    v7_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1)) | (~spl6_15 | ~spl6_16)),
% 1.32/0.56    inference(subsumption_resolution,[],[f406,f397])).
% 1.32/0.56  fof(f397,plain,(
% 1.32/0.56    v2_pre_topc(sK3(sK0,sK1)) | ~spl6_15),
% 1.32/0.56    inference(subsumption_resolution,[],[f393,f307])).
% 1.32/0.56  fof(f393,plain,(
% 1.32/0.56    v2_pre_topc(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1)) | ~spl6_15),
% 1.32/0.56    inference(resolution,[],[f311,f84])).
% 1.32/0.56  fof(f84,plain,(
% 1.32/0.56    ( ! [X0] : (~v2_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f31])).
% 1.32/0.56  fof(f31,plain,(
% 1.32/0.56    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(flattening,[],[f30])).
% 1.32/0.56  fof(f30,plain,(
% 1.32/0.56    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f16])).
% 1.32/0.56  fof(f16,axiom,(
% 1.32/0.56    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.32/0.56  fof(f311,plain,(
% 1.32/0.56    v2_tdlat_3(sK3(sK0,sK1)) | ~spl6_15),
% 1.32/0.56    inference(subsumption_resolution,[],[f310,f73])).
% 1.32/0.56  fof(f310,plain,(
% 1.32/0.56    v2_tdlat_3(sK3(sK0,sK1)) | v2_struct_0(sK0) | ~spl6_15),
% 1.32/0.56    inference(subsumption_resolution,[],[f309,f74])).
% 1.32/0.56  fof(f309,plain,(
% 1.32/0.56    v2_tdlat_3(sK3(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_15),
% 1.32/0.56    inference(subsumption_resolution,[],[f308,f75])).
% 1.32/0.56  fof(f75,plain,(
% 1.32/0.56    v2_tdlat_3(sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f57])).
% 1.32/0.56  fof(f308,plain,(
% 1.32/0.56    v2_tdlat_3(sK3(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_15),
% 1.32/0.56    inference(subsumption_resolution,[],[f296,f76])).
% 1.32/0.56  fof(f296,plain,(
% 1.32/0.56    v2_tdlat_3(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_15),
% 1.32/0.56    inference(resolution,[],[f243,f93])).
% 1.32/0.56  fof(f93,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f40])).
% 1.32/0.56  fof(f40,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(flattening,[],[f39])).
% 1.32/0.56  fof(f39,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f18])).
% 1.32/0.56  fof(f18,axiom,(
% 1.32/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.32/0.56  fof(f406,plain,(
% 1.32/0.56    v7_struct_0(sK3(sK0,sK1)) | ~v2_pre_topc(sK3(sK0,sK1)) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1)) | (~spl6_15 | ~spl6_16)),
% 1.32/0.56    inference(subsumption_resolution,[],[f279,f311])).
% 1.32/0.56  fof(f279,plain,(
% 1.32/0.56    ~v2_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | ~v2_pre_topc(sK3(sK0,sK1)) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1)) | ~spl6_16),
% 1.32/0.56    inference(resolution,[],[f252,f86])).
% 1.32/0.56  fof(f86,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f33])).
% 1.32/0.56  fof(f33,plain,(
% 1.32/0.56    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(flattening,[],[f32])).
% 1.32/0.56  fof(f32,plain,(
% 1.32/0.56    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f17])).
% 1.32/0.56  fof(f17,axiom,(
% 1.32/0.56    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.32/0.56  fof(f252,plain,(
% 1.32/0.56    v1_tdlat_3(sK3(sK0,sK1)) | ~spl6_16),
% 1.32/0.56    inference(avatar_component_clause,[],[f250])).
% 1.32/0.56  fof(f405,plain,(
% 1.32/0.56    ~spl6_21 | ~spl6_34 | spl6_2 | ~spl6_14),
% 1.32/0.56    inference(avatar_split_clause,[],[f325,f232,f120,f402,f287])).
% 1.32/0.56  fof(f120,plain,(
% 1.32/0.56    spl6_2 <=> v1_zfmisc_1(sK1)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.32/0.56  fof(f232,plain,(
% 1.32/0.56    spl6_14 <=> sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.32/0.56  fof(f325,plain,(
% 1.32/0.56    v1_zfmisc_1(sK1) | ~l1_struct_0(sK3(sK0,sK1)) | ~v7_struct_0(sK3(sK0,sK1)) | ~spl6_14),
% 1.32/0.56    inference(superposition,[],[f102,f234])).
% 1.32/0.56  fof(f234,plain,(
% 1.32/0.56    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl6_14),
% 1.32/0.56    inference(avatar_component_clause,[],[f232])).
% 1.32/0.56  fof(f102,plain,(
% 1.32/0.56    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f46])).
% 1.32/0.56  fof(f46,plain,(
% 1.32/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.32/0.56    inference(flattening,[],[f45])).
% 1.32/0.56  fof(f45,plain,(
% 1.32/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f13])).
% 1.32/0.56  fof(f13,axiom,(
% 1.32/0.56    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.32/0.56  fof(f278,plain,(
% 1.32/0.56    spl6_1 | spl6_19),
% 1.32/0.56    inference(avatar_split_clause,[],[f273,f275,f116])).
% 1.32/0.56  fof(f273,plain,(
% 1.32/0.56    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f272,f73])).
% 1.32/0.56  fof(f272,plain,(
% 1.32/0.56    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f271,f74])).
% 1.32/0.56  fof(f271,plain,(
% 1.32/0.56    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f131,f76])).
% 1.32/0.56  fof(f131,plain,(
% 1.32/0.56    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f95])).
% 1.32/0.56  fof(f95,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f61])).
% 1.32/0.56  fof(f270,plain,(
% 1.32/0.56    spl6_1 | spl6_18),
% 1.32/0.56    inference(avatar_split_clause,[],[f265,f267,f116])).
% 1.32/0.56  fof(f265,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | v2_tex_2(sK1,sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f264,f73])).
% 1.32/0.56  fof(f264,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f263,f74])).
% 1.32/0.56  fof(f263,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f132,f76])).
% 1.32/0.56  fof(f132,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f96])).
% 1.32/0.56  fof(f96,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f61])).
% 1.32/0.56  fof(f262,plain,(
% 1.32/0.56    ~spl6_17 | ~spl6_1),
% 1.32/0.56    inference(avatar_split_clause,[],[f257,f116,f259])).
% 1.32/0.56  fof(f257,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 1.32/0.56    inference(subsumption_resolution,[],[f256,f73])).
% 1.32/0.56  fof(f256,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f255,f74])).
% 1.32/0.56  fof(f255,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f254,f76])).
% 1.32/0.56  fof(f254,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f133,f77])).
% 1.32/0.56  fof(f77,plain,(
% 1.32/0.56    ~v1_xboole_0(sK1)),
% 1.32/0.56    inference(cnf_transformation,[],[f57])).
% 1.32/0.56  fof(f133,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f98])).
% 1.32/0.56  fof(f98,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK3(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f63])).
% 1.32/0.56  fof(f63,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f62])).
% 1.32/0.56  fof(f62,plain,(
% 1.32/0.56    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f44,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(flattening,[],[f43])).
% 1.32/0.56  fof(f43,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f24])).
% 1.32/0.56  fof(f24,plain,(
% 1.32/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.32/0.56    inference(pure_predicate_removal,[],[f20])).
% 1.32/0.56  fof(f20,axiom,(
% 1.32/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 1.32/0.56  fof(f253,plain,(
% 1.32/0.56    spl6_16 | ~spl6_1),
% 1.32/0.56    inference(avatar_split_clause,[],[f248,f116,f250])).
% 1.32/0.56  fof(f248,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1))),
% 1.32/0.56    inference(subsumption_resolution,[],[f247,f73])).
% 1.32/0.56  fof(f247,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1)) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f246,f74])).
% 1.32/0.56  fof(f246,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f245,f76])).
% 1.32/0.56  fof(f245,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f134,f77])).
% 1.32/0.56  fof(f134,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f99])).
% 1.32/0.56  fof(f99,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK3(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f63])).
% 1.32/0.56  fof(f244,plain,(
% 1.32/0.56    spl6_15 | ~spl6_1),
% 1.32/0.56    inference(avatar_split_clause,[],[f239,f116,f241])).
% 1.32/0.56  fof(f239,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f238,f73])).
% 1.32/0.56  fof(f238,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f237,f74])).
% 1.32/0.56  fof(f237,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f236,f76])).
% 1.32/0.56  fof(f236,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f135,f77])).
% 1.32/0.56  fof(f135,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f100])).
% 1.32/0.56  fof(f100,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK3(X0,X1),X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f63])).
% 1.32/0.56  fof(f235,plain,(
% 1.32/0.56    spl6_14 | ~spl6_1),
% 1.32/0.56    inference(avatar_split_clause,[],[f230,f116,f232])).
% 1.32/0.56  fof(f230,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.32/0.56    inference(subsumption_resolution,[],[f229,f73])).
% 1.32/0.56  fof(f229,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f228,f74])).
% 1.32/0.56  fof(f228,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f227,f76])).
% 1.32/0.56  fof(f227,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f136,f77])).
% 1.32/0.56  fof(f136,plain,(
% 1.32/0.56    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f78,f101])).
% 1.32/0.56  fof(f101,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK3(X0,X1)) = X1 | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f63])).
% 1.32/0.56  fof(f226,plain,(
% 1.32/0.56    spl6_12 | spl6_13 | spl6_1 | ~spl6_2),
% 1.32/0.56    inference(avatar_split_clause,[],[f217,f120,f116,f223,f219])).
% 1.32/0.56  fof(f217,plain,(
% 1.32/0.56    sK1 = sK2(sK0,sK1) | v1_xboole_0(sK2(sK0,sK1)) | (spl6_1 | ~spl6_2)),
% 1.32/0.56    inference(subsumption_resolution,[],[f216,f77])).
% 1.32/0.56  fof(f216,plain,(
% 1.32/0.56    sK1 = sK2(sK0,sK1) | v1_xboole_0(sK1) | v1_xboole_0(sK2(sK0,sK1)) | (spl6_1 | ~spl6_2)),
% 1.32/0.56    inference(subsumption_resolution,[],[f215,f121])).
% 1.32/0.56  fof(f121,plain,(
% 1.32/0.56    v1_zfmisc_1(sK1) | ~spl6_2),
% 1.32/0.56    inference(avatar_component_clause,[],[f120])).
% 1.32/0.56  fof(f215,plain,(
% 1.32/0.56    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | v1_xboole_0(sK2(sK0,sK1)) | spl6_1),
% 1.32/0.56    inference(resolution,[],[f165,f82])).
% 1.32/0.56  fof(f82,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f28])).
% 1.32/0.56  fof(f28,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.32/0.56    inference(flattening,[],[f27])).
% 1.32/0.56  fof(f27,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f19])).
% 1.32/0.56  fof(f19,axiom,(
% 1.32/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.32/0.56  fof(f165,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | spl6_1),
% 1.32/0.56    inference(subsumption_resolution,[],[f164,f73])).
% 1.32/0.56  fof(f164,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.56    inference(subsumption_resolution,[],[f163,f74])).
% 1.32/0.56  fof(f163,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.56    inference(subsumption_resolution,[],[f162,f76])).
% 1.32/0.56  fof(f162,plain,(
% 1.32/0.56    r1_tarski(sK2(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_1),
% 1.32/0.56    inference(subsumption_resolution,[],[f132,f118])).
% 1.32/0.56  fof(f124,plain,(
% 1.32/0.56    spl6_1 | spl6_2),
% 1.32/0.56    inference(avatar_split_clause,[],[f79,f120,f116])).
% 1.32/0.56  fof(f79,plain,(
% 1.32/0.56    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f57])).
% 1.32/0.56  fof(f123,plain,(
% 1.32/0.56    ~spl6_1 | ~spl6_2),
% 1.32/0.56    inference(avatar_split_clause,[],[f80,f120,f116])).
% 1.32/0.56  fof(f80,plain,(
% 1.32/0.56    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f57])).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (23619)------------------------------
% 1.32/0.56  % (23619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (23619)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (23619)Memory used [KB]: 10874
% 1.32/0.56  % (23619)Time elapsed: 0.147 s
% 1.32/0.56  % (23619)------------------------------
% 1.32/0.56  % (23619)------------------------------
% 1.32/0.56  % (23610)Success in time 0.206 s
%------------------------------------------------------------------------------
