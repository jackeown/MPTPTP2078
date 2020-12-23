%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 105 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  169 ( 227 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f48,f53,f65,f70,f82,f90])).

fof(f90,plain,
    ( spl1_3
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl1_3
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f88,f47])).

fof(f47,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_3
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f88,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f87,f23])).

fof(f23,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f87,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_subset_1(k2_struct_0(sK0))
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f86,f69])).

fof(f69,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl1_6
  <=> m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f86,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_subset_1(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_pre_topc(sK0,k2_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_subset_1(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_8 ),
    inference(superposition,[],[f29,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_8
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | k2_subset_1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f82,plain,
    ( spl1_8
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f74,f68,f63,f80])).

fof(f63,plain,
    ( spl1_5
  <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f74,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f73,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_5 ),
    inference(resolution,[],[f64,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f64,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f73,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_6 ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f70,plain,
    ( spl1_6
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f61,f51,f37,f68])).

fof(f37,plain,
    ( spl1_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f51,plain,
    ( spl1_4
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f61,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f60,f23])).

fof(f60,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f57,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f55,f38])).

fof(f38,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f55,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl1_4 ),
    inference(superposition,[],[f24,f52])).

fof(f52,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f65,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f59,f51,f37,f63])).

fof(f59,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f58,f23])).

fof(f58,plain,
    ( r1_tarski(k2_subset_1(k2_struct_0(sK0)),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))))
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f54,f38])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl1_4 ),
    inference(superposition,[],[f25,f52])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f53,plain,
    ( spl1_4
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f49,f42,f51])).

fof(f42,plain,
    ( spl1_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f49,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f43,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f48,plain,(
    ~ spl1_3 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f44,plain,
    ( spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f40,f37,f42])).

fof(f40,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (15389)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (15382)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (15394)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (15382)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f39,f44,f48,f53,f65,f70,f82,f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl1_3 | ~spl1_6 | ~spl1_8),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    $false | (spl1_3 | ~spl1_6 | ~spl1_8)),
% 0.20/0.46    inference(subsumption_resolution,[],[f88,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) | spl1_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl1_3 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | (~spl1_6 | ~spl1_8)),
% 0.20/0.46    inference(forward_demodulation,[],[f87,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_subset_1(k2_struct_0(sK0)) | (~spl1_6 | ~spl1_8)),
% 0.20/0.46    inference(subsumption_resolution,[],[f86,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl1_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    spl1_6 <=> m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_subset_1(k2_struct_0(sK0)) | ~m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl1_8),
% 0.20/0.46    inference(subsumption_resolution,[],[f85,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ~r1_tarski(k1_xboole_0,k2_pre_topc(sK0,k2_struct_0(sK0))) | k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_subset_1(k2_struct_0(sK0)) | ~m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl1_8),
% 0.20/0.46    inference(superposition,[],[f29,f81])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | ~spl1_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    spl1_8 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl1_8 | ~spl1_5 | ~spl1_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f74,f68,f63,f80])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl1_5 <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.46    inference(forward_demodulation,[],[f73,f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | ~spl1_5),
% 0.20/0.46    inference(resolution,[],[f64,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | ~spl1_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f63])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | ~spl1_6),
% 0.20/0.46    inference(resolution,[],[f69,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl1_6 | ~spl1_1 | ~spl1_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f61,f51,f37,f68])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl1_1 <=> l1_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl1_4 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl1_1 | ~spl1_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f60,f23])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    m1_subset_1(k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl1_1 | ~spl1_4)),
% 0.20/0.46    inference(resolution,[],[f57,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl1_1 | ~spl1_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f55,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    l1_pre_topc(sK0) | ~spl1_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl1_4),
% 0.20/0.46    inference(superposition,[],[f24,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f51])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl1_5 | ~spl1_1 | ~spl1_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f59,f51,f37,f63])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | (~spl1_1 | ~spl1_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f58,f23])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    r1_tarski(k2_subset_1(k2_struct_0(sK0)),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))) | (~spl1_1 | ~spl1_4)),
% 0.20/0.46    inference(resolution,[],[f56,f30])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | (~spl1_1 | ~spl1_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f54,f38])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl1_4),
% 0.20/0.46    inference(superposition,[],[f25,f52])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl1_4 | ~spl1_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f49,f42,f51])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl1_2 <=> l1_struct_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_2),
% 0.20/0.46    inference(resolution,[],[f43,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    l1_struct_0(sK0) | ~spl1_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f42])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ~spl1_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f46])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.20/0.46    inference(negated_conjecture,[],[f11])).
% 0.20/0.46  fof(f11,conjecture,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl1_2 | ~spl1_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f40,f37,f42])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    l1_struct_0(sK0) | ~spl1_1),
% 0.20/0.46    inference(resolution,[],[f38,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl1_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f37])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15382)------------------------------
% 0.20/0.46  % (15382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15382)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15382)Memory used [KB]: 6140
% 0.20/0.46  % (15382)Time elapsed: 0.078 s
% 0.20/0.46  % (15382)------------------------------
% 0.20/0.46  % (15382)------------------------------
% 0.20/0.47  % (15381)Success in time 0.114 s
%------------------------------------------------------------------------------
