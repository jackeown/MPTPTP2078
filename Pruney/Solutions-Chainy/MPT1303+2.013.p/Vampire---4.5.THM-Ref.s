%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  98 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 426 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(resolution,[],[f206,f50])).

fof(f50,plain,(
    ~ v1_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f24,f43])).

fof(f43,plain,(
    ! [X1] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2)) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f24,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f206,plain,(
    ! [X0] : v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) ),
    inference(subsumption_resolution,[],[f205,f20])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f205,plain,(
    ! [X0] :
      ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f204,f23])).

fof(f23,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f204,plain,(
    ! [X0] :
      ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)
      | ~ v1_tops_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    ! [X0] :
      ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f127,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f34,f51])).

fof(f51,plain,(
    ! [X0] : k8_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k1_setfam_1(k2_tarski(sK1,X0)) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k8_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | v1_tops_2(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_tops_2(X2,X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:00:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.20/0.42  % (2675)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.43  % (2675)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f254,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(resolution,[],[f206,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ~v1_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.22/0.44    inference(backward_demodulation,[],[f24,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X1] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f32,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f29,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f206,plain,(
% 0.22/0.44    ( ! [X0] : (v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f205,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    l1_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f205,plain,(
% 0.22/0.44    ( ! [X0] : (v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f204,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    v1_tops_2(sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f204,plain,(
% 0.22/0.44    ( ! [X0] : (v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) | ~v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f184,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f184,plain,(
% 0.22/0.44    ( ! [X0] : (v1_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(resolution,[],[f127,f59])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.22/0.44    inference(backward_demodulation,[],[f34,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (k8_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k1_setfam_1(k2_tarski(sK1,X0))) )),
% 0.22/0.44    inference(resolution,[],[f33,f21])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f30,f27])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(k8_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.22/0.44    inference(resolution,[],[f28,f21])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | v1_tops_2(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~v1_tops_2(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.22/0.44    inference(resolution,[],[f25,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f26,f27])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_tops_2(X2,X0) | v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (2675)------------------------------
% 0.22/0.44  % (2675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (2675)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (2675)Memory used [KB]: 2046
% 0.22/0.44  % (2675)Time elapsed: 0.021 s
% 0.22/0.44  % (2675)------------------------------
% 0.22/0.44  % (2675)------------------------------
% 0.22/0.44  % (2661)Success in time 0.077 s
%------------------------------------------------------------------------------
