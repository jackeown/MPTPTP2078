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
% DateTime   : Thu Dec  3 13:11:01 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 219 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f118,f150])).

fof(f150,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl2_3 ),
    inference(resolution,[],[f117,f25])).

fof(f25,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(sK0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,X1),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f117,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_3
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f118,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f110,f42,f115])).

fof(f42,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f109,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f94,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

% (26289)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(u1_struct_0(X1),X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(X1),X0),u1_struct_0(X1))
      | r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(X1),X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f82,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f82,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(k2_pre_topc(X3,k3_subset_1(u1_struct_0(X3),X4)),k1_zfmisc_1(u1_struct_0(X3)))
      | r1_tarski(k1_tops_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(X3),X4),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_tops_1(X3,X4),X4)
      | ~ m1_subset_1(k2_pre_topc(X3,k3_subset_1(u1_struct_0(X3),X4)),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(X3),X4),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_pre_topc(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f26,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(u1_struct_0(X0),X2),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | r1_tarski(k1_tops_1(X0,X1),X2)
      | ~ m1_subset_1(k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f51,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f44,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:11:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.43  % (26286)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.44  % (26294)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.44  % (26292)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.44  % (26281)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.44  % (26291)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.18/0.45  % (26284)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.45  % (26283)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.45  % (26279)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.45  % (26283)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % (26290)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f151,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(avatar_sat_refutation,[],[f51,f118,f150])).
% 0.18/0.45  fof(f150,plain,(
% 0.18/0.45    ~spl2_3),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f149])).
% 0.18/0.45  fof(f149,plain,(
% 0.18/0.45    $false | ~spl2_3),
% 0.18/0.45    inference(resolution,[],[f117,f25])).
% 0.18/0.45  fof(f25,plain,(
% 0.18/0.45    ~r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.18/0.45    inference(cnf_transformation,[],[f21])).
% 0.18/0.45  fof(f21,plain,(
% 0.18/0.45    (~r1_tarski(k1_tops_1(sK0,sK1),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).
% 0.18/0.45  fof(f19,plain,(
% 0.18/0.45    ? [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k1_tops_1(sK0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f20,plain,(
% 0.18/0.45    ? [X1] : (~r1_tarski(k1_tops_1(sK0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,sK1),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f11,plain,(
% 0.18/0.45    ? [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.18/0.45    inference(ennf_transformation,[],[f10])).
% 0.18/0.45  fof(f10,negated_conjecture,(
% 0.18/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.18/0.45    inference(negated_conjecture,[],[f9])).
% 0.18/0.45  fof(f9,conjecture,(
% 0.18/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.18/0.45  fof(f117,plain,(
% 0.18/0.45    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_3),
% 0.18/0.45    inference(avatar_component_clause,[],[f115])).
% 0.18/0.45  fof(f115,plain,(
% 0.18/0.45    spl2_3 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.18/0.45  fof(f118,plain,(
% 0.18/0.45    spl2_3 | ~spl2_1),
% 0.18/0.45    inference(avatar_split_clause,[],[f110,f42,f115])).
% 0.18/0.45  fof(f42,plain,(
% 0.18/0.45    spl2_1 <=> l1_pre_topc(sK0)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.45  fof(f110,plain,(
% 0.18/0.45    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.18/0.45    inference(resolution,[],[f109,f24])).
% 0.18/0.45  fof(f24,plain,(
% 0.18/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.45    inference(cnf_transformation,[],[f21])).
% 0.18/0.45  fof(f109,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.18/0.45    inference(duplicate_literal_removal,[],[f104])).
% 0.18/0.45  fof(f104,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.18/0.45    inference(resolution,[],[f94,f52])).
% 0.18/0.45  fof(f52,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.45    inference(superposition,[],[f35,f36])).
% 0.18/0.45  fof(f36,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.45    inference(definition_unfolding,[],[f30,f29])).
% 0.18/0.45  fof(f29,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f1])).
% 0.18/0.45  fof(f1,axiom,(
% 0.18/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.45  % (26289)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.45  fof(f30,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f14])).
% 0.18/0.45  fof(f14,plain,(
% 0.18/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f3])).
% 0.18/0.45  fof(f3,axiom,(
% 0.18/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.18/0.45  fof(f35,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.18/0.45    inference(definition_unfolding,[],[f28,f29])).
% 0.18/0.45  fof(f28,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f2])).
% 0.18/0.45  fof(f2,axiom,(
% 0.18/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.18/0.45  fof(f94,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(u1_struct_0(X1),X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,X0),X0)) )),
% 0.18/0.45    inference(duplicate_literal_removal,[],[f91])).
% 0.18/0.45  fof(f91,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~r1_tarski(k3_subset_1(u1_struct_0(X1),X0),u1_struct_0(X1)) | r1_tarski(k1_tops_1(X1,X0),X0) | ~r1_tarski(k3_subset_1(u1_struct_0(X1),X0),u1_struct_0(X1))) )),
% 0.18/0.45    inference(resolution,[],[f90,f34])).
% 0.18/0.45  fof(f34,plain,(
% 0.18/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f22])).
% 0.18/0.45  fof(f22,plain,(
% 0.18/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.18/0.45    inference(nnf_transformation,[],[f5])).
% 0.18/0.45  fof(f5,axiom,(
% 0.18/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.45  fof(f90,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(k3_subset_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.18/0.45    inference(duplicate_literal_removal,[],[f86])).
% 0.18/0.45  fof(f86,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(k3_subset_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.45    inference(resolution,[],[f82,f32])).
% 0.18/0.45  fof(f32,plain,(
% 0.18/0.45    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f18,plain,(
% 0.18/0.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.18/0.45    inference(flattening,[],[f17])).
% 0.18/0.45  fof(f17,plain,(
% 0.18/0.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f6])).
% 0.18/0.45  fof(f6,axiom,(
% 0.18/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.18/0.45  fof(f82,plain,(
% 0.18/0.45    ( ! [X4,X3] : (~m1_subset_1(k2_pre_topc(X3,k3_subset_1(u1_struct_0(X3),X4)),k1_zfmisc_1(u1_struct_0(X3))) | r1_tarski(k1_tops_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(k3_subset_1(u1_struct_0(X3),X4),u1_struct_0(X3))) )),
% 0.18/0.45    inference(duplicate_literal_removal,[],[f77])).
% 0.18/0.45  fof(f77,plain,(
% 0.18/0.45    ( ! [X4,X3] : (r1_tarski(k1_tops_1(X3,X4),X4) | ~m1_subset_1(k2_pre_topc(X3,k3_subset_1(u1_struct_0(X3),X4)),k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~l1_pre_topc(X3) | ~r1_tarski(k3_subset_1(u1_struct_0(X3),X4),u1_struct_0(X3))) )),
% 0.18/0.45    inference(resolution,[],[f57,f40])).
% 0.18/0.45  fof(f40,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_pre_topc(X1,X0)) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) )),
% 0.18/0.45    inference(resolution,[],[f26,f34])).
% 0.18/0.45  fof(f26,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  fof(f12,plain,(
% 0.18/0.45    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.45    inference(ennf_transformation,[],[f7])).
% 0.18/0.45  fof(f7,axiom,(
% 0.18/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.18/0.45  fof(f57,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(u1_struct_0(X0),X2),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | r1_tarski(k1_tops_1(X0,X1),X2) | ~m1_subset_1(k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.45    inference(superposition,[],[f31,f27])).
% 0.18/0.45  fof(f27,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f13])).
% 0.18/0.45  fof(f13,plain,(
% 0.18/0.45    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.45    inference(ennf_transformation,[],[f8])).
% 0.18/0.45  fof(f8,axiom,(
% 0.18/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.18/0.45  fof(f31,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  fof(f16,plain,(
% 0.18/0.45    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.45    inference(flattening,[],[f15])).
% 0.18/0.45  fof(f15,plain,(
% 0.18/0.45    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f4])).
% 0.18/0.45  fof(f4,axiom,(
% 0.18/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 0.18/0.45  fof(f51,plain,(
% 0.18/0.45    spl2_1),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f50])).
% 0.18/0.45  fof(f50,plain,(
% 0.18/0.45    $false | spl2_1),
% 0.18/0.45    inference(resolution,[],[f44,f23])).
% 0.18/0.45  fof(f23,plain,(
% 0.18/0.45    l1_pre_topc(sK0)),
% 0.18/0.45    inference(cnf_transformation,[],[f21])).
% 0.18/0.45  fof(f44,plain,(
% 0.18/0.45    ~l1_pre_topc(sK0) | spl2_1),
% 0.18/0.45    inference(avatar_component_clause,[],[f42])).
% 0.18/0.45  % SZS output end Proof for theBenchmark
% 0.18/0.45  % (26283)------------------------------
% 0.18/0.45  % (26283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (26283)Termination reason: Refutation
% 0.18/0.45  
% 0.18/0.45  % (26283)Memory used [KB]: 6140
% 0.18/0.45  % (26283)Time elapsed: 0.058 s
% 0.18/0.45  % (26296)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.18/0.45  % (26283)------------------------------
% 0.18/0.45  % (26283)------------------------------
% 0.18/0.45  % (26293)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.18/0.45  % (26282)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.46  % (26278)Success in time 0.125 s
%------------------------------------------------------------------------------
