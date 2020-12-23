%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 231 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  206 ( 749 expanded)
%              Number of equality atoms :   16 ( 102 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1040,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f128,f1026,f1039])).

fof(f1039,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f1038])).

fof(f1038,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f91,f969])).

fof(f969,plain,
    ( ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1))
    | ~ spl9_1 ),
    inference(resolution,[],[f772,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f772,plain,
    ( ! [X0] : r2_hidden(sK2,k1_zfmisc_1(X0))
    | ~ spl9_1 ),
    inference(resolution,[],[f708,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f708,plain,
    ( ! [X11] : r1_tarski(sK2,X11)
    | ~ spl9_1 ),
    inference(resolution,[],[f700,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f700,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f88,f22])).

fof(f88,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f91,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl9_2
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1026,plain,(
    ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f1024,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK1)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f254,f200])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f129,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl9_5 ),
    inference(resolution,[],[f127,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f127,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f254,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f249,f84])).

fof(f84,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f17,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f17,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).

fof(f249,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f214,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | sQ8_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f42,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f214,plain,(
    ~ sQ8_eqProxy(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f150,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sQ8_eqProxy(X0,X1)
      | sQ8_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f56])).

fof(f150,plain,(
    ~ sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f143,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f143,plain,
    ( ~ sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ8_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f28,f56])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ sQ8_eqProxy(X0,k3_subset_1(sK0,sK2))
      | ~ sQ8_eqProxy(sK1,X0) ) ),
    inference(resolution,[],[f58,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ8_eqProxy(X0,X1)
      | ~ sQ8_eqProxy(X1,X2)
      | sQ8_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f56])).

fof(f58,plain,(
    ~ sQ8_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f19,f56])).

fof(f19,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1024,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK1)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f1023,f257])).

fof(f257,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f251,f255])).

fof(f251,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f214,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | sQ8_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f44,f56])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1023,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f1015])).

fof(f1015,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f168,f214])).

fof(f168,plain,(
    ! [X26,X25] :
      ( sQ8_eqProxy(k4_xboole_0(sK0,X25),X26)
      | r2_hidden(sK7(sK0,X25,X26),sK2)
      | r2_hidden(sK7(sK0,X25,X26),X26)
      | r2_hidden(sK7(sK0,X25,X26),sK1) ) ),
    inference(resolution,[],[f81,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | sQ8_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f43,f56])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f16,f26])).

fof(f16,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f128,plain,
    ( spl9_5
    | spl9_2 ),
    inference(avatar_split_clause,[],[f76,f90,f125])).

fof(f76,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f93,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f72,f90,f86])).

fof(f72,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 14:17:38 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.41  % (4789)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.16/0.42  % (4781)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.16/0.42  % (4769)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.16/0.43  % (4773)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.16/0.44  % (4767)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.16/0.44  % (4785)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.16/0.45  % (4777)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.16/0.45  % (4775)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.16/0.45  % (4777)Refutation not found, incomplete strategy% (4777)------------------------------
% 0.16/0.45  % (4777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.45  % (4777)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.45  
% 0.16/0.45  % (4777)Memory used [KB]: 10618
% 0.16/0.45  % (4777)Time elapsed: 0.103 s
% 0.16/0.45  % (4777)------------------------------
% 0.16/0.45  % (4777)------------------------------
% 0.16/0.45  % (4783)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.16/0.45  % (4783)Refutation not found, incomplete strategy% (4783)------------------------------
% 0.16/0.45  % (4783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.45  % (4783)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.45  
% 0.16/0.45  % (4783)Memory used [KB]: 10618
% 0.16/0.45  % (4783)Time elapsed: 0.103 s
% 0.16/0.45  % (4783)------------------------------
% 0.16/0.45  % (4783)------------------------------
% 0.16/0.46  % (4793)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.16/0.47  % (4771)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.16/0.47  % (4768)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.16/0.48  % (4774)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.16/0.48  % (4795)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.16/0.48  % (4770)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.16/0.48  % (4779)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.16/0.48  % (4792)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.16/0.49  % (4787)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.16/0.49  % (4766)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.16/0.49  % (4794)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.16/0.50  % (4772)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.16/0.50  % (4790)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.16/0.50  % (4791)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.16/0.51  % (4784)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.16/0.51  % (4786)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.16/0.51  % (4782)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.16/0.51  % (4786)Refutation not found, incomplete strategy% (4786)------------------------------
% 0.16/0.51  % (4786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.51  % (4786)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.51  
% 0.16/0.51  % (4786)Memory used [KB]: 10874
% 0.16/0.51  % (4786)Time elapsed: 0.153 s
% 0.16/0.51  % (4786)------------------------------
% 0.16/0.51  % (4786)------------------------------
% 0.16/0.51  % (4776)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.16/0.51  % (4778)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.51  % (4776)Refutation not found, incomplete strategy% (4776)------------------------------
% 0.16/0.51  % (4776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.51  % (4776)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.51  
% 0.16/0.51  % (4776)Memory used [KB]: 10618
% 0.16/0.51  % (4776)Time elapsed: 0.154 s
% 0.16/0.51  % (4776)------------------------------
% 0.16/0.51  % (4776)------------------------------
% 0.16/0.52  % (4780)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.16/0.52  % (4788)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.71/0.54  % (4779)Refutation found. Thanks to Tanya!
% 1.71/0.54  % SZS status Theorem for theBenchmark
% 1.71/0.54  % SZS output start Proof for theBenchmark
% 1.71/0.54  fof(f1040,plain,(
% 1.71/0.54    $false),
% 1.71/0.54    inference(avatar_sat_refutation,[],[f93,f128,f1026,f1039])).
% 1.71/0.54  fof(f1039,plain,(
% 1.71/0.54    ~spl9_1 | ~spl9_2),
% 1.71/0.54    inference(avatar_contradiction_clause,[],[f1038])).
% 1.71/0.54  fof(f1038,plain,(
% 1.71/0.54    $false | (~spl9_1 | ~spl9_2)),
% 1.71/0.54    inference(subsumption_resolution,[],[f91,f969])).
% 1.71/0.54  fof(f969,plain,(
% 1.71/0.54    ( ! [X1] : (~v1_xboole_0(k1_zfmisc_1(X1))) ) | ~spl9_1),
% 1.71/0.54    inference(resolution,[],[f772,f22])).
% 1.71/0.54  fof(f22,plain,(
% 1.71/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.71/0.54    inference(cnf_transformation,[],[f1])).
% 1.71/0.54  fof(f1,axiom,(
% 1.71/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.71/0.54  fof(f772,plain,(
% 1.71/0.54    ( ! [X0] : (r2_hidden(sK2,k1_zfmisc_1(X0))) ) | ~spl9_1),
% 1.71/0.54    inference(resolution,[],[f708,f49])).
% 1.71/0.54  fof(f49,plain,(
% 1.71/0.54    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.71/0.54    inference(equality_resolution,[],[f32])).
% 1.71/0.54  fof(f32,plain,(
% 1.71/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.71/0.54    inference(cnf_transformation,[],[f6])).
% 1.71/0.54  fof(f6,axiom,(
% 1.71/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.71/0.54  fof(f708,plain,(
% 1.71/0.54    ( ! [X11] : (r1_tarski(sK2,X11)) ) | ~spl9_1),
% 1.71/0.54    inference(resolution,[],[f700,f30])).
% 1.71/0.54  fof(f30,plain,(
% 1.71/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.71/0.54    inference(cnf_transformation,[],[f15])).
% 1.71/0.54  fof(f15,plain,(
% 1.71/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.71/0.54    inference(ennf_transformation,[],[f2])).
% 1.71/0.54  fof(f2,axiom,(
% 1.71/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.71/0.54  fof(f700,plain,(
% 1.71/0.54    ( ! [X3] : (~r2_hidden(X3,sK2)) ) | ~spl9_1),
% 1.71/0.54    inference(resolution,[],[f88,f22])).
% 1.71/0.54  fof(f88,plain,(
% 1.71/0.54    v1_xboole_0(sK2) | ~spl9_1),
% 1.71/0.54    inference(avatar_component_clause,[],[f86])).
% 1.71/0.54  fof(f86,plain,(
% 1.71/0.54    spl9_1 <=> v1_xboole_0(sK2)),
% 1.71/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.71/0.54  fof(f91,plain,(
% 1.71/0.54    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl9_2),
% 1.71/0.54    inference(avatar_component_clause,[],[f90])).
% 1.71/0.54  fof(f90,plain,(
% 1.71/0.54    spl9_2 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.71/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.71/0.54  fof(f1026,plain,(
% 1.71/0.54    ~spl9_5),
% 1.71/0.54    inference(avatar_contradiction_clause,[],[f1025])).
% 1.71/0.54  fof(f1025,plain,(
% 1.71/0.54    $false | ~spl9_5),
% 1.71/0.54    inference(subsumption_resolution,[],[f1024,f255])).
% 1.71/0.54  fof(f255,plain,(
% 1.71/0.54    ~r2_hidden(sK7(sK0,sK2,sK1),sK1) | ~spl9_5),
% 1.71/0.54    inference(subsumption_resolution,[],[f254,f200])).
% 1.71/0.54  fof(f200,plain,(
% 1.71/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl9_5),
% 1.71/0.54    inference(resolution,[],[f129,f29])).
% 1.71/0.54  fof(f29,plain,(
% 1.71/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.71/0.54    inference(cnf_transformation,[],[f15])).
% 1.71/0.54  fof(f129,plain,(
% 1.71/0.54    r1_tarski(sK1,sK0) | ~spl9_5),
% 1.71/0.54    inference(resolution,[],[f127,f48])).
% 1.71/0.54  fof(f48,plain,(
% 1.71/0.54    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.71/0.54    inference(equality_resolution,[],[f33])).
% 1.71/0.54  fof(f33,plain,(
% 1.71/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.71/0.54    inference(cnf_transformation,[],[f6])).
% 1.71/0.54  fof(f127,plain,(
% 1.71/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl9_5),
% 1.71/0.54    inference(avatar_component_clause,[],[f125])).
% 1.71/0.54  fof(f125,plain,(
% 1.71/0.54    spl9_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.71/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.71/0.54  fof(f254,plain,(
% 1.71/0.54    ~r2_hidden(sK7(sK0,sK2,sK1),sK0) | ~r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 1.71/0.54    inference(subsumption_resolution,[],[f249,f84])).
% 1.71/0.54  fof(f84,plain,(
% 1.71/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.71/0.54    inference(subsumption_resolution,[],[f83,f22])).
% 1.71/0.54  fof(f83,plain,(
% 1.71/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 1.71/0.54    inference(resolution,[],[f17,f26])).
% 1.71/0.54  fof(f26,plain,(
% 1.71/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.71/0.54    inference(cnf_transformation,[],[f13])).
% 1.71/0.54  fof(f13,plain,(
% 1.71/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.71/0.54    inference(ennf_transformation,[],[f7])).
% 1.71/0.54  fof(f7,axiom,(
% 1.71/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.71/0.54  fof(f17,plain,(
% 1.71/0.54    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 1.71/0.54    inference(cnf_transformation,[],[f12])).
% 1.71/0.54  fof(f12,plain,(
% 1.71/0.54    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.71/0.54    inference(flattening,[],[f11])).
% 1.71/0.54  fof(f11,plain,(
% 1.71/0.54    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.71/0.54    inference(ennf_transformation,[],[f10])).
% 1.71/0.54  fof(f10,negated_conjecture,(
% 1.71/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 1.71/0.54    inference(negated_conjecture,[],[f9])).
% 1.71/0.54  fof(f9,conjecture,(
% 1.71/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).
% 1.71/0.54  fof(f249,plain,(
% 1.71/0.54    ~r2_hidden(sK7(sK0,sK2,sK1),sK0) | r2_hidden(sK7(sK0,sK2,sK1),sK2) | ~r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 1.71/0.54    inference(resolution,[],[f214,f67])).
% 1.71/0.54  fof(f67,plain,(
% 1.71/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2) | sQ8_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 1.71/0.54    inference(equality_proxy_replacement,[],[f42,f56])).
% 1.71/0.54  fof(f56,plain,(
% 1.71/0.54    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 1.71/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 1.71/0.54  fof(f42,plain,(
% 1.71/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.71/0.54    inference(cnf_transformation,[],[f4])).
% 1.71/0.54  fof(f4,axiom,(
% 1.71/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.71/0.54  fof(f214,plain,(
% 1.71/0.54    ~sQ8_eqProxy(k4_xboole_0(sK0,sK2),sK1)),
% 1.71/0.54    inference(resolution,[],[f150,f69])).
% 1.71/0.54  fof(f69,plain,(
% 1.71/0.54    ( ! [X0,X1] : (~sQ8_eqProxy(X0,X1) | sQ8_eqProxy(X1,X0)) )),
% 1.71/0.54    inference(equality_proxy_axiom,[],[f56])).
% 1.71/0.54  fof(f150,plain,(
% 1.71/0.54    ~sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2))),
% 1.71/0.54    inference(subsumption_resolution,[],[f143,f18])).
% 1.71/0.54  fof(f18,plain,(
% 1.71/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.71/0.54    inference(cnf_transformation,[],[f12])).
% 1.71/0.54  fof(f143,plain,(
% 1.71/0.54    ~sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.71/0.54    inference(resolution,[],[f78,f59])).
% 1.71/0.54  fof(f59,plain,(
% 1.71/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ8_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1))) )),
% 1.71/0.54    inference(equality_proxy_replacement,[],[f28,f56])).
% 1.71/0.54  fof(f28,plain,(
% 1.71/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.71/0.54    inference(cnf_transformation,[],[f14])).
% 1.71/0.54  fof(f14,plain,(
% 1.71/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.71/0.54    inference(ennf_transformation,[],[f8])).
% 1.71/0.54  fof(f8,axiom,(
% 1.71/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.71/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.71/0.54  fof(f78,plain,(
% 1.71/0.54    ( ! [X0] : (~sQ8_eqProxy(X0,k3_subset_1(sK0,sK2)) | ~sQ8_eqProxy(sK1,X0)) )),
% 1.71/0.54    inference(resolution,[],[f58,f70])).
% 1.71/0.54  fof(f70,plain,(
% 1.71/0.54    ( ! [X2,X0,X1] : (~sQ8_eqProxy(X0,X1) | ~sQ8_eqProxy(X1,X2) | sQ8_eqProxy(X0,X2)) )),
% 1.71/0.54    inference(equality_proxy_axiom,[],[f56])).
% 1.71/0.54  fof(f58,plain,(
% 1.71/0.54    ~sQ8_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 1.71/0.54    inference(equality_proxy_replacement,[],[f19,f56])).
% 1.71/0.54  fof(f19,plain,(
% 1.71/0.54    sK1 != k3_subset_1(sK0,sK2)),
% 1.71/0.54    inference(cnf_transformation,[],[f12])).
% 1.71/0.56  fof(f1024,plain,(
% 1.71/0.56    r2_hidden(sK7(sK0,sK2,sK1),sK1) | ~spl9_5),
% 1.71/0.56    inference(subsumption_resolution,[],[f1023,f257])).
% 1.71/0.56  fof(f257,plain,(
% 1.71/0.56    ~r2_hidden(sK7(sK0,sK2,sK1),sK2) | ~spl9_5),
% 1.71/0.56    inference(subsumption_resolution,[],[f251,f255])).
% 1.71/0.56  fof(f251,plain,(
% 1.71/0.56    ~r2_hidden(sK7(sK0,sK2,sK1),sK2) | r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 1.71/0.56    inference(resolution,[],[f214,f65])).
% 1.71/0.56  fof(f65,plain,(
% 1.71/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | sQ8_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 1.71/0.56    inference(equality_proxy_replacement,[],[f44,f56])).
% 1.71/0.56  fof(f44,plain,(
% 1.71/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.71/0.56    inference(cnf_transformation,[],[f4])).
% 1.71/0.56  fof(f1023,plain,(
% 1.71/0.56    r2_hidden(sK7(sK0,sK2,sK1),sK2) | r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 1.71/0.56    inference(duplicate_literal_removal,[],[f1015])).
% 1.71/0.56  fof(f1015,plain,(
% 1.71/0.56    r2_hidden(sK7(sK0,sK2,sK1),sK2) | r2_hidden(sK7(sK0,sK2,sK1),sK1) | r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 1.71/0.56    inference(resolution,[],[f168,f214])).
% 1.71/0.56  fof(f168,plain,(
% 1.71/0.56    ( ! [X26,X25] : (sQ8_eqProxy(k4_xboole_0(sK0,X25),X26) | r2_hidden(sK7(sK0,X25,X26),sK2) | r2_hidden(sK7(sK0,X25,X26),X26) | r2_hidden(sK7(sK0,X25,X26),sK1)) )),
% 1.71/0.56    inference(resolution,[],[f81,f66])).
% 1.71/0.56  fof(f66,plain,(
% 1.71/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | sQ8_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 1.71/0.56    inference(equality_proxy_replacement,[],[f43,f56])).
% 1.71/0.56  fof(f43,plain,(
% 1.71/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.71/0.56    inference(cnf_transformation,[],[f4])).
% 1.71/0.56  fof(f81,plain,(
% 1.71/0.56    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 1.71/0.56    inference(subsumption_resolution,[],[f80,f22])).
% 1.71/0.56  fof(f80,plain,(
% 1.71/0.56    ( ! [X1] : (r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 1.71/0.56    inference(resolution,[],[f16,f26])).
% 1.71/0.56  fof(f16,plain,(
% 1.71/0.56    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 1.71/0.56    inference(cnf_transformation,[],[f12])).
% 1.71/0.56  fof(f128,plain,(
% 1.71/0.56    spl9_5 | spl9_2),
% 1.71/0.56    inference(avatar_split_clause,[],[f76,f90,f125])).
% 1.71/0.56  fof(f76,plain,(
% 1.71/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.71/0.56    inference(resolution,[],[f20,f27])).
% 1.71/0.56  fof(f27,plain,(
% 1.71/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.71/0.56    inference(cnf_transformation,[],[f13])).
% 1.71/0.56  fof(f20,plain,(
% 1.71/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.71/0.56    inference(cnf_transformation,[],[f12])).
% 1.71/0.56  fof(f93,plain,(
% 1.71/0.56    spl9_1 | ~spl9_2),
% 1.71/0.56    inference(avatar_split_clause,[],[f72,f90,f86])).
% 1.71/0.56  fof(f72,plain,(
% 1.71/0.56    ~v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(sK2)),
% 1.71/0.56    inference(resolution,[],[f18,f25])).
% 1.71/0.56  fof(f25,plain,(
% 1.71/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 1.71/0.56    inference(cnf_transformation,[],[f13])).
% 1.71/0.56  % SZS output end Proof for theBenchmark
% 1.71/0.56  % (4779)------------------------------
% 1.71/0.56  % (4779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.56  % (4779)Termination reason: Refutation
% 1.71/0.56  
% 1.71/0.56  % (4779)Memory used [KB]: 6780
% 1.71/0.56  % (4779)Time elapsed: 0.196 s
% 1.71/0.56  % (4779)------------------------------
% 1.71/0.56  % (4779)------------------------------
% 1.71/0.57  % (4765)Success in time 0.244 s
%------------------------------------------------------------------------------
