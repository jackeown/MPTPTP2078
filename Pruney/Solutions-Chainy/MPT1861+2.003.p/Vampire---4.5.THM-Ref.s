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
% DateTime   : Thu Dec  3 13:20:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 367 expanded)
%              Number of leaves         :   10 (  93 expanded)
%              Depth                    :   24
%              Number of atoms          :  145 (1027 expanded)
%              Number of equality atoms :   21 ( 170 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16618)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f177,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f177,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(resolution,[],[f172,f43])).

fof(f43,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f21,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f170,f125])).

fof(f125,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f124,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f124,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f123,f21])).

fof(f123,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f122,f24])).

fof(f122,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)
      | ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f39,f56])).

fof(f56,plain,(
    ~ v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f20,f46])).

fof(f46,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k4_xboole_0(X1,k4_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k1_enumset1(X0,X0,sK2)) ),
    inference(resolution,[],[f19,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,X0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f103,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f102,f19])).

fof(f102,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f99,f83])).

fof(f83,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),sK2) ),
    inference(superposition,[],[f24,f66])).

fof(f66,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f61,f37])).

fof(f61,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f40,f48])).

fof(f48,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(forward_demodulation,[],[f44,f37])).

fof(f44,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k1_enumset1(sK2,sK2,X0)) ),
    inference(superposition,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f99,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f59,f18])).

fof(f18,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f149,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f149,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)),X1)
      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f127,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)),X0)
      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) ) ),
    inference(resolution,[],[f126,f29])).

fof(f126,plain,(
    r2_hidden(sK3(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f125,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (16609)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.49  % (16617)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.49  % (16625)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (16625)Refutation not found, incomplete strategy% (16625)------------------------------
% 0.22/0.50  % (16625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16625)Memory used [KB]: 10746
% 0.22/0.50  % (16625)Time elapsed: 0.096 s
% 0.22/0.50  % (16625)------------------------------
% 0.22/0.50  % (16625)------------------------------
% 0.22/0.51  % (16632)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (16615)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (16607)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (16608)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (16616)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (16631)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (16612)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (16624)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (16613)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (16624)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  % (16618)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)),
% 0.22/0.54    inference(resolution,[],[f172,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f21,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f125])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f124,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f123,f21])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f122,f24])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f103,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) | ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(resolution,[],[f39,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ~v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 0.22/0.54    inference(backward_demodulation,[],[f20,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k4_xboole_0(X1,k4_xboole_0(X1,sK2))) )),
% 0.22/0.54    inference(superposition,[],[f40,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k1_enumset1(X0,X0,sK2))) )),
% 0.22/0.54    inference(resolution,[],[f19,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f34,f35])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(resolution,[],[f22,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    v2_tex_2(sK1,sK0) | ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f102,f19])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X2] : (r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),sK2)) )),
% 0.22/0.54    inference(superposition,[],[f24,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) )),
% 0.22/0.54    inference(superposition,[],[f61,f37])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) )),
% 0.22/0.54    inference(backward_demodulation,[],[f40,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f44,f37])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k1_enumset1(sK2,sK2,X0))) )),
% 0.22/0.54    inference(superposition,[],[f40,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f27,f27])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | ~m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f59,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) | ~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0))) )),
% 0.22/0.54    inference(resolution,[],[f149,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)),X1) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f127,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)),X0) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) )),
% 0.22/0.54    inference(resolution,[],[f126,f29])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    r2_hidden(sK3(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),u1_struct_0(sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.54    inference(resolution,[],[f125,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (16624)------------------------------
% 0.22/0.54  % (16624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16624)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (16624)Memory used [KB]: 1791
% 0.22/0.54  % (16624)Time elapsed: 0.097 s
% 0.22/0.54  % (16624)------------------------------
% 0.22/0.54  % (16624)------------------------------
% 0.22/0.54  % (16602)Success in time 0.169 s
%------------------------------------------------------------------------------
