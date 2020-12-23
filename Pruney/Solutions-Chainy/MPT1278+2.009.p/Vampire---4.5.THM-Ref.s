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
% DateTime   : Thu Dec  3 13:12:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 153 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  217 ( 841 expanded)
%              Number of equality atoms :   23 ( 135 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f102,f128])).

fof(f128,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f126,f17])).

fof(f17,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK1
      & v3_tops_1(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f126,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f125,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f124,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f122,f21])).

fof(f21,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f118,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tops_1)).

fof(f118,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f117,f18])).

fof(f117,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f114,f19])).

fof(f114,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f113,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(k1_tops_1(X0,X1),k1_xboole_0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f23,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f113,plain,
    ( ~ sQ2_eqProxy(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl3_4 ),
    inference(resolution,[],[f108,f52])).

fof(f52,plain,(
    ! [X2] :
      ( ~ sQ2_eqProxy(X2,sK1)
      | ~ sQ2_eqProxy(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sQ2_eqProxy(k1_xboole_0,X0)
      | ~ sQ2_eqProxy(X0,sK1) ) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f22,f28])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sQ2_eqProxy(X0,X2)
      | ~ sQ2_eqProxy(X1,X2)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f108,plain,
    ( sQ2_eqProxy(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f107,f20])).

fof(f20,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,
    ( sQ2_eqProxy(k1_tops_1(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f106,f18])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | sQ2_eqProxy(k1_tops_1(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f86,f19])).

fof(f86,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | sQ2_eqProxy(k1_tops_1(X1,X3),X3)
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

% (11706)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (11701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (11701)Refutation not found, incomplete strategy% (11701)------------------------------
% (11701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11701)Termination reason: Refutation not found, incomplete strategy

% (11701)Memory used [KB]: 1535
% (11701)Time elapsed: 0.066 s
% (11701)------------------------------
% (11701)------------------------------
fof(f85,plain,
    ( spl3_4
  <=> ! [X1,X3] :
        ( sQ2_eqProxy(k1_tops_1(X1,X3),X3)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f102,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f100,f18])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f98,f17])).

fof(f98,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f19])).

fof(f83,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_3
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f33,f85,f82])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ2_eqProxy(k1_tops_1(X1,X3),X3)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f28])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.44  % (11693)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.44  % (11696)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.45  % (11693)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f129,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f87,f102,f128])).
% 0.22/0.45  fof(f128,plain,(
% 0.22/0.45    ~spl3_4),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f127])).
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    $false | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f126,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    v2_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f6])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.22/0.45    inference(negated_conjecture,[],[f4])).
% 0.22/0.45  fof(f4,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    ~v2_pre_topc(sK0) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f125,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    l1_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f125,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f124,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f122,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v3_tops_1(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    ~v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_4),
% 0.22/0.45    inference(resolution,[],[f118,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tops_1)).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    ~v2_tops_1(sK1,sK0) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f117,f18])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    ~v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f114,f19])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.45    inference(resolution,[],[f113,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X0,X1] : (sQ2_eqProxy(k1_tops_1(X0,X1),k1_xboole_0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.45    inference(equality_proxy_replacement,[],[f23,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.45    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    ~sQ2_eqProxy(k1_tops_1(sK0,sK1),k1_xboole_0) | ~spl3_4),
% 0.22/0.45    inference(resolution,[],[f108,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ( ! [X2] : (~sQ2_eqProxy(X2,sK1) | ~sQ2_eqProxy(X2,k1_xboole_0)) )),
% 0.22/0.45    inference(resolution,[],[f48,f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.22/0.45    inference(equality_proxy_axiom,[],[f28])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0] : (~sQ2_eqProxy(k1_xboole_0,X0) | ~sQ2_eqProxy(X0,sK1)) )),
% 0.22/0.45    inference(resolution,[],[f45,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ~sQ2_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.45    inference(equality_proxy_replacement,[],[f22,f28])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    k1_xboole_0 != sK1),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (sQ2_eqProxy(X0,X2) | ~sQ2_eqProxy(X1,X2) | ~sQ2_eqProxy(X0,X1)) )),
% 0.22/0.45    inference(equality_proxy_axiom,[],[f28])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    sQ2_eqProxy(k1_tops_1(sK0,sK1),sK1) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f107,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    v3_pre_topc(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    sQ2_eqProxy(k1_tops_1(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~spl3_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f106,f18])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | sQ2_eqProxy(k1_tops_1(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~spl3_4),
% 0.22/0.45    inference(resolution,[],[f86,f19])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | sQ2_eqProxy(k1_tops_1(X1,X3),X3) | ~v3_pre_topc(X3,X1)) ) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f85])).
% 0.22/0.45  % (11706)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.46  % (11701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.46  % (11701)Refutation not found, incomplete strategy% (11701)------------------------------
% 0.22/0.46  % (11701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (11701)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (11701)Memory used [KB]: 1535
% 0.22/0.46  % (11701)Time elapsed: 0.066 s
% 0.22/0.46  % (11701)------------------------------
% 0.22/0.46  % (11701)------------------------------
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    spl3_4 <=> ! [X1,X3] : (sQ2_eqProxy(k1_tops_1(X1,X3),X3) | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    ~spl3_3),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.46  fof(f101,plain,(
% 0.22/0.46    $false | ~spl3_3),
% 0.22/0.46    inference(subsumption_resolution,[],[f100,f18])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    ~l1_pre_topc(sK0) | ~spl3_3),
% 0.22/0.46    inference(subsumption_resolution,[],[f98,f17])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.22/0.46    inference(resolution,[],[f83,f19])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f82])).
% 0.22/0.46  fof(f82,plain,(
% 0.22/0.46    spl3_3 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    spl3_3 | spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f33,f85,f82])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (sQ2_eqProxy(k1_tops_1(X1,X3),X3) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(equality_proxy_replacement,[],[f25,f28])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (11693)------------------------------
% 0.22/0.46  % (11693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (11693)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (11693)Memory used [KB]: 6140
% 0.22/0.46  % (11693)Time elapsed: 0.058 s
% 0.22/0.46  % (11693)------------------------------
% 0.22/0.46  % (11693)------------------------------
% 0.22/0.46  % (11687)Success in time 0.103 s
%------------------------------------------------------------------------------
