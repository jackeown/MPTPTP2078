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
% DateTime   : Thu Dec  3 13:00:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 (  93 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  138 ( 292 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f24,f28,f32,f40,f47,f51,f55,f61])).

fof(f61,plain,
    ( ~ spl2_4
    | ~ spl2_8
    | ~ spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f57,f49,f45,f53,f30])).

fof(f30,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( spl2_8
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f45,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f49,plain,
    ( spl2_7
  <=> r2_hidden(sK1,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f57,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | spl2_7 ),
    inference(resolution,[],[f50,f16])).

fof(f16,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

% (11557)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (11561)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (11555)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (11563)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f50,plain,
    ( ~ r2_hidden(sK1,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f43,f36,f26,f53])).

fof(f26,plain,
    ( spl2_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f43,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f27,f37])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f27,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f51,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f42,f36,f18,f49])).

fof(f18,plain,
    ( spl2_1
  <=> r2_hidden(sK1,k1_funct_2(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( ~ r2_hidden(sK1,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f19,f37])).

fof(f19,plain,
    ( ~ r2_hidden(sK1,k1_funct_2(sK0,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f47,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f41,f36,f22,f45])).

fof(f22,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f23,f37])).

fof(f23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f40,plain,
    ( spl2_5
    | ~ spl2_3
    | ~ spl2_2
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f34,f30,f18,f22,f26,f36])).

fof(f34,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f33,f19])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1,k1_funct_2(X1,X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK1,X1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_4 ),
    inference(resolution,[],[f14,f31])).

fof(f31,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f10,f30])).

fof(f10,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r2_hidden(sK1,k1_funct_2(sK0,sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ~ r2_hidden(sK1,k1_funct_2(sK0,sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).

fof(f28,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f18])).

fof(f13,plain,(
    ~ r2_hidden(sK1,k1_funct_2(sK0,sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.46  % (11554)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.47  % (11560)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.47  % (11569)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.47  % (11560)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f62,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f20,f24,f28,f32,f40,f47,f51,f55,f61])).
% 0.18/0.47  fof(f61,plain,(
% 0.18/0.47    ~spl2_4 | ~spl2_8 | ~spl2_6 | spl2_7),
% 0.18/0.47    inference(avatar_split_clause,[],[f57,f49,f45,f53,f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    spl2_4 <=> v1_funct_1(sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    spl2_8 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    spl2_7 <=> r2_hidden(sK1,k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.18/0.47  fof(f57,plain,(
% 0.18/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | spl2_7),
% 0.18/0.47    inference(resolution,[],[f50,f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ( ! [X2,X1] : (r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.18/0.47    inference(equality_resolution,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f7])).
% 0.18/0.47  % (11557)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.47  % (11561)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.48  % (11555)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (11563)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.18/0.48  fof(f7,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.18/0.48    inference(flattening,[],[f6])).
% 0.18/0.48  fof(f6,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.18/0.48    inference(ennf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).
% 0.18/0.48  fof(f50,plain,(
% 0.18/0.48    ~r2_hidden(sK1,k1_funct_2(k1_xboole_0,k1_xboole_0)) | spl2_7),
% 0.18/0.48    inference(avatar_component_clause,[],[f49])).
% 0.18/0.48  fof(f55,plain,(
% 0.18/0.48    spl2_8 | ~spl2_3 | ~spl2_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f43,f36,f26,f53])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    spl2_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    spl2_5 <=> k1_xboole_0 = sK0),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.18/0.48  fof(f43,plain,(
% 0.18/0.48    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 0.18/0.48    inference(superposition,[],[f27,f37])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | ~spl2_5),
% 0.18/0.48    inference(avatar_component_clause,[],[f36])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    v1_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 0.18/0.48    inference(avatar_component_clause,[],[f26])).
% 0.18/0.48  fof(f51,plain,(
% 0.18/0.48    ~spl2_7 | spl2_1 | ~spl2_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f42,f36,f18,f49])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    spl2_1 <=> r2_hidden(sK1,k1_funct_2(sK0,sK0))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    ~r2_hidden(sK1,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (spl2_1 | ~spl2_5)),
% 0.18/0.48    inference(superposition,[],[f19,f37])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ~r2_hidden(sK1,k1_funct_2(sK0,sK0)) | spl2_1),
% 0.18/0.48    inference(avatar_component_clause,[],[f18])).
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    spl2_6 | ~spl2_2 | ~spl2_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f41,f36,f22,f45])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.18/0.48  fof(f41,plain,(
% 0.18/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_2 | ~spl2_5)),
% 0.18/0.48    inference(superposition,[],[f23,f37])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f22])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    spl2_5 | ~spl2_3 | ~spl2_2 | spl2_1 | ~spl2_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f34,f30,f18,f22,f26,f36])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | (spl2_1 | ~spl2_4)),
% 0.18/0.48    inference(resolution,[],[f33,f19])).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    ( ! [X0,X1] : (r2_hidden(sK1,k1_funct_2(X1,X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | k1_xboole_0 = X0) ) | ~spl2_4),
% 0.18/0.48    inference(resolution,[],[f14,f31])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    v1_funct_1(sK1) | ~spl2_4),
% 0.18/0.48    inference(avatar_component_clause,[],[f30])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    spl2_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f10,f30])).
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    v1_funct_1(sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,plain,(
% 0.18/0.48    ~r2_hidden(sK1,k1_funct_2(sK0,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.18/0.48  fof(f8,plain,(
% 0.18/0.48    ? [X0,X1] : (~r2_hidden(X1,k1_funct_2(X0,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (~r2_hidden(sK1,k1_funct_2(sK0,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f5,plain,(
% 0.18/0.48    ? [X0,X1] : (~r2_hidden(X1,k1_funct_2(X0,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.18/0.48    inference(flattening,[],[f4])).
% 0.18/0.48  fof(f4,plain,(
% 0.18/0.48    ? [X0,X1] : (~r2_hidden(X1,k1_funct_2(X0,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 0.18/0.48    inference(negated_conjecture,[],[f2])).
% 0.18/0.48  fof(f2,conjecture,(
% 0.18/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    spl2_3),
% 0.18/0.48    inference(avatar_split_clause,[],[f11,f26])).
% 0.18/0.48  fof(f11,plain,(
% 0.18/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    spl2_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f12,f22])).
% 0.18/0.48  fof(f12,plain,(
% 0.18/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ~spl2_1),
% 0.18/0.48    inference(avatar_split_clause,[],[f13,f18])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ~r2_hidden(sK1,k1_funct_2(sK0,sK0))),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (11560)------------------------------
% 0.18/0.48  % (11560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (11560)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (11560)Memory used [KB]: 10618
% 0.18/0.48  % (11560)Time elapsed: 0.071 s
% 0.18/0.48  % (11560)------------------------------
% 0.18/0.48  % (11560)------------------------------
% 0.18/0.48  % (11553)Success in time 0.136 s
%------------------------------------------------------------------------------
