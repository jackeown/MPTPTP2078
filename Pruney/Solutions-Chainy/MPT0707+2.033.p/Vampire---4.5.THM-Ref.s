%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 196 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f60,f70,f72,f76])).

fof(f76,plain,
    ( ~ spl3_4
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f74,f67,f42,f64])).

fof(f64,plain,
    ( spl3_4
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( spl3_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_5
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f74,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f73,f30])).

fof(f30,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f32,f68])).

fof(f68,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f72,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f65,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f65,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f70,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f62,f58,f67,f64])).

fof(f58,plain,
    ( spl3_3
  <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f59])).

fof(f59,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f60,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f46,f58])).

fof(f46,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f55,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k6_relat_1(X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)) ) ),
    inference(global_subsumption,[],[f27,f54])).

fof(f54,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f49,f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f27,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f44,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:24:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (3038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.40  % (3038)Refutation not found, incomplete strategy% (3038)------------------------------
% 0.20/0.40  % (3038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (3038)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.40  
% 0.20/0.40  % (3038)Memory used [KB]: 1535
% 0.20/0.40  % (3038)Time elapsed: 0.002 s
% 0.20/0.40  % (3038)------------------------------
% 0.20/0.40  % (3038)------------------------------
% 0.20/0.44  % (3028)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.44  % (3028)Refutation not found, incomplete strategy% (3028)------------------------------
% 0.20/0.44  % (3028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (3028)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (3028)Memory used [KB]: 10618
% 0.20/0.44  % (3028)Time elapsed: 0.034 s
% 0.20/0.44  % (3028)------------------------------
% 0.20/0.44  % (3028)------------------------------
% 0.20/0.45  % (3039)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (3031)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (3031)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f44,f48,f60,f70,f72,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ~spl3_4 | spl3_1 | ~spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f74,f67,f42,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl3_4 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl3_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl3_5 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~spl3_5),
% 0.20/0.46    inference(forward_demodulation,[],[f73,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK0)) | ~spl3_5),
% 0.20/0.46    inference(superposition,[],[f32,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    $false | spl3_4),
% 0.20/0.46    inference(resolution,[],[f65,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~v1_relat_1(k6_relat_1(sK0)) | spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f64])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ~spl3_4 | spl3_5 | ~spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f62,f58,f67,f64])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    spl3_3 <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~spl3_3),
% 0.20/0.46    inference(superposition,[],[f31,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f58])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl3_3 | ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f56,f46,f58])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | ~spl3_2),
% 0.20/0.46    inference(resolution,[],[f55,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k6_relat_1(X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) )),
% 0.20/0.46    inference(global_subsumption,[],[f27,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X2,X3] : (k6_relat_1(X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)) | v1_xboole_0(k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 0.20/0.46    inference(resolution,[],[f51,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.46    inference(resolution,[],[f50,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(equality_resolution,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.46    inference(rectify,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f49,f30])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.46    inference(resolution,[],[f33,f28])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f46])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f42])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (3031)------------------------------
% 0.20/0.46  % (3031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3031)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (3031)Memory used [KB]: 10618
% 0.20/0.46  % (3031)Time elapsed: 0.033 s
% 0.20/0.46  % (3031)------------------------------
% 0.20/0.46  % (3031)------------------------------
% 0.20/0.46  % (3024)Success in time 0.112 s
%------------------------------------------------------------------------------
