%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 127 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  184 ( 324 expanded)
%              Number of equality atoms :   36 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f48,f52,f60,f81,f91,f124,f177,f182,f197,f203])).

fof(f203,plain,
    ( ~ spl2_3
    | spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f202,f122,f43,f50])).

fof(f50,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f43,plain,
    ( spl2_2
  <=> sK0 = k5_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f122,plain,
    ( spl2_15
  <=> sK0 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_2
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_2
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f200,f123])).

fof(f123,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f200,plain,
    ( sK0 != k3_tarski(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f44,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f44,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f197,plain,
    ( spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f195,f122,f40])).

fof(f40,plain,
    ( spl2_1
  <=> m1_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f195,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl2_15 ),
    inference(superposition,[],[f68,f123])).

fof(f68,plain,(
    ! [X1] : m1_setfam_1(X1,k3_tarski(X1)) ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f56,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f30,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f182,plain,
    ( spl2_14
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f180,f40,f119])).

fof(f119,plain,
    ( spl2_14
  <=> r1_tarski(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f180,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f177,plain,
    ( ~ spl2_3
    | spl2_15
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f174,f43,f122,f50])).

fof(f174,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f47,f32])).

fof(f47,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f124,plain,
    ( ~ spl2_14
    | spl2_15
    | spl2_8 ),
    inference(avatar_split_clause,[],[f110,f89,f122,f119])).

fof(f89,plain,
    ( spl2_8
  <=> r2_xboole_0(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f110,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ r1_tarski(sK0,k3_tarski(sK1))
    | spl2_8 ),
    inference(resolution,[],[f35,f90])).

fof(f90,plain,
    ( ~ r2_xboole_0(sK0,k3_tarski(sK1))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f91,plain,
    ( ~ spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f79,f89])).

fof(f79,plain,
    ( spl2_6
  <=> r1_tarski(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f83,plain,
    ( ~ r2_xboole_0(sK0,k3_tarski(sK1))
    | ~ spl2_6 ),
    inference(resolution,[],[f80,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f80,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f77,f58,f79])).

fof(f58,plain,
    ( spl2_4
  <=> r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f77,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f75,f29])).

fof(f29,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f75,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f31,f59])).

fof(f59,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f60,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f55,f50,f58])).

fof(f55,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f36,f51])).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 != k5_setfam_1(sK0,sK1)
      | ~ m1_setfam_1(sK1,sK0) )
    & ( sK0 = k5_setfam_1(sK0,sK1)
      | m1_setfam_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( sK0 != k5_setfam_1(sK0,sK1)
        | ~ m1_setfam_1(sK1,sK0) )
      & ( sK0 = k5_setfam_1(sK0,sK1)
        | m1_setfam_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f48,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f26,f43,f40])).

fof(f26,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f43,f40])).

fof(f27,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | ~ m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (1116)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (1118)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (1116)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f45,f48,f52,f60,f81,f91,f124,f177,f182,f197,f203])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ~spl2_3 | spl2_2 | ~spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f202,f122,f43,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl2_2 <=> sK0 = k5_setfam_1(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl2_15 <=> sK0 = k3_tarski(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl2_2 | ~spl2_15)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f201])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    sK0 != sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl2_2 | ~spl2_15)),
% 0.21/0.47    inference(forward_demodulation,[],[f200,f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    sK0 = k3_tarski(sK1) | ~spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f122])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    sK0 != k3_tarski(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl2_2),
% 0.21/0.47    inference(superposition,[],[f44,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    sK0 != k5_setfam_1(sK0,sK1) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    spl2_1 | ~spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f195,f122,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl2_1 <=> m1_setfam_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    m1_setfam_1(sK1,sK0) | ~spl2_15),
% 0.21/0.47    inference(superposition,[],[f68,f123])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X1] : (m1_setfam_1(X1,k3_tarski(X1))) )),
% 0.21/0.47    inference(resolution,[],[f56,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f36,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f30,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl2_14 | ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f180,f40,f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl2_14 <=> r1_tarski(sK0,k3_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    r1_tarski(sK0,k3_tarski(sK1)) | ~spl2_1),
% 0.21/0.47    inference(resolution,[],[f46,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    m1_setfam_1(sK1,sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    ~spl2_3 | spl2_15 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f174,f43,f122,f50])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    sK0 = k3_tarski(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 0.21/0.47    inference(superposition,[],[f47,f32])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    sK0 = k5_setfam_1(sK0,sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~spl2_14 | spl2_15 | spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f110,f89,f122,f119])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl2_8 <=> r2_xboole_0(sK0,k3_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    sK0 = k3_tarski(sK1) | ~r1_tarski(sK0,k3_tarski(sK1)) | spl2_8),
% 0.21/0.47    inference(resolution,[],[f35,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~r2_xboole_0(sK0,k3_tarski(sK1)) | spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ~spl2_8 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f83,f79,f89])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl2_6 <=> r1_tarski(k3_tarski(sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~r2_xboole_0(sK0,k3_tarski(sK1)) | ~spl2_6),
% 0.21/0.47    inference(resolution,[],[f80,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(sK1),sK0) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl2_6 | ~spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f77,f58,f79])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl2_4 <=> r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(sK1),sK0) | ~spl2_4),
% 0.21/0.47    inference(forward_demodulation,[],[f75,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(sK0))) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f31,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    r1_tarski(sK1,k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl2_4 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f50,f58])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    r1_tarski(sK1,k1_zfmisc_1(sK0)) | ~spl2_3),
% 0.21/0.47    inference(resolution,[],[f36,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f50])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    (sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1] : (((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1] : ((m1_setfam_1(X1,X0) <~> k5_setfam_1(X0,X1) = X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f43,f40])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f43,f40])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (1116)------------------------------
% 0.21/0.47  % (1116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1116)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (1116)Memory used [KB]: 10746
% 0.21/0.47  % (1116)Time elapsed: 0.053 s
% 0.21/0.47  % (1116)------------------------------
% 0.21/0.47  % (1116)------------------------------
% 0.21/0.47  % (1109)Success in time 0.107 s
%------------------------------------------------------------------------------
