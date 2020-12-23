%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 186 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  169 ( 867 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f845,plain,(
    $false ),
    inference(resolution,[],[f844,f119])).

fof(f119,plain,(
    ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f26,f112])).

fof(f112,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(X1,sK2)) = k9_subset_1(u1_struct_0(sK0),X1,sK2) ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f844,plain,(
    ! [X0] : v2_tex_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) ),
    inference(resolution,[],[f841,f835])).

fof(f835,plain,(
    ! [X58] :
      ( ~ v2_tex_2(sK1,sK0)
      | v2_tex_2(k1_setfam_1(k2_tarski(sK1,X58)),sK0) ) ),
    inference(subsumption_resolution,[],[f834,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f834,plain,(
    ! [X58] :
      ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,X58)),sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f794,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f794,plain,(
    ! [X58] :
      ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,X58)),sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f288,f62])).

fof(f62,plain,(
    ! [X2] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f55,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,sK1)
      | r1_tarski(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f288,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X12,X14)),k1_zfmisc_1(u1_struct_0(X13)))
      | v2_tex_2(k1_setfam_1(k2_tarski(X12,X14)),X13)
      | ~ v2_tex_2(X12,X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ l1_pre_topc(X13) ) ),
    inference(resolution,[],[f27,f35])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f841,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f839,f119])).

fof(f839,plain,(
    ! [X0] :
      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0)
      | v2_tex_2(sK1,sK0) ) ),
    inference(superposition,[],[f838,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f838,plain,(
    ! [X0] :
      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0)
      | v2_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f837,f25])).

fof(f25,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f837,plain,(
    ! [X59] :
      ( ~ v2_tex_2(sK2,sK0)
      | v2_tex_2(k1_setfam_1(k2_tarski(sK2,X59)),sK0) ) ),
    inference(subsumption_resolution,[],[f836,f22])).

fof(f836,plain,(
    ! [X59] :
      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X59)),sK0)
      | ~ v2_tex_2(sK2,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f795,f24])).

fof(f795,plain,(
    ! [X59] :
      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X59)),sK0)
      | ~ v2_tex_2(sK2,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f288,f70])).

fof(f70,plain,(
    ! [X2] : m1_subset_1(k1_setfam_1(k2_tarski(sK2,X2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f59,f32])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,sK2)
      | r1_tarski(X7,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f31,f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.41  % (2460)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.44  % (2460)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f845,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(resolution,[],[f844,f119])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.22/0.44    inference(backward_demodulation,[],[f26,f112])).
% 0.22/0.44  fof(f112,plain,(
% 0.22/0.44    ( ! [X1] : (k1_setfam_1(k2_tarski(X1,sK2)) = k9_subset_1(u1_struct_0(sK0),X1,sK2)) )),
% 0.22/0.44    inference(resolution,[],[f36,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f8])).
% 0.22/0.44  fof(f8,conjecture,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f33,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f844,plain,(
% 0.22/0.44    ( ! [X0] : (v2_tex_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)) )),
% 0.22/0.44    inference(resolution,[],[f841,f835])).
% 0.22/0.44  fof(f835,plain,(
% 0.22/0.44    ( ! [X58] : (~v2_tex_2(sK1,sK0) | v2_tex_2(k1_setfam_1(k2_tarski(sK1,X58)),sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f834,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    l1_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f834,plain,(
% 0.22/0.44    ( ! [X58] : (v2_tex_2(k1_setfam_1(k2_tarski(sK1,X58)),sK0) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f794,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f794,plain,(
% 0.22/0.44    ( ! [X58] : (v2_tex_2(k1_setfam_1(k2_tarski(sK1,X58)),sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(resolution,[],[f288,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X2] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X2)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.44    inference(resolution,[],[f57,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.44    inference(nnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f55,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f28,f30])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ( ! [X6] : (~r1_tarski(X6,sK1) | r1_tarski(X6,u1_struct_0(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f34,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f31,f23])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.44  fof(f288,plain,(
% 0.22/0.44    ( ! [X14,X12,X13] : (~m1_subset_1(k1_setfam_1(k2_tarski(X12,X14)),k1_zfmisc_1(u1_struct_0(X13))) | v2_tex_2(k1_setfam_1(k2_tarski(X12,X14)),X13) | ~v2_tex_2(X12,X13) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X13))) | ~l1_pre_topc(X13)) )),
% 0.22/0.44    inference(resolution,[],[f27,f35])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.22/0.44  fof(f841,plain,(
% 0.22/0.44    v2_tex_2(sK1,sK0)),
% 0.22/0.44    inference(resolution,[],[f839,f119])).
% 0.22/0.44  fof(f839,plain,(
% 0.22/0.44    ( ! [X0] : (v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) | v2_tex_2(sK1,sK0)) )),
% 0.22/0.44    inference(superposition,[],[f838,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.44  fof(f838,plain,(
% 0.22/0.44    ( ! [X0] : (v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) | v2_tex_2(sK1,sK0)) )),
% 0.22/0.44    inference(resolution,[],[f837,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f837,plain,(
% 0.22/0.44    ( ! [X59] : (~v2_tex_2(sK2,sK0) | v2_tex_2(k1_setfam_1(k2_tarski(sK2,X59)),sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f836,f22])).
% 0.22/0.44  fof(f836,plain,(
% 0.22/0.44    ( ! [X59] : (v2_tex_2(k1_setfam_1(k2_tarski(sK2,X59)),sK0) | ~v2_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f795,f24])).
% 0.22/0.44  fof(f795,plain,(
% 0.22/0.44    ( ! [X59] : (v2_tex_2(k1_setfam_1(k2_tarski(sK2,X59)),sK0) | ~v2_tex_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.44    inference(resolution,[],[f288,f70])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X2] : (m1_subset_1(k1_setfam_1(k2_tarski(sK2,X2)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.44    inference(resolution,[],[f59,f32])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f56,f35])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X7] : (~r1_tarski(X7,sK2) | r1_tarski(X7,u1_struct_0(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f34,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f31,f24])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (2460)------------------------------
% 0.22/0.44  % (2460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (2460)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (2460)Memory used [KB]: 2430
% 0.22/0.44  % (2460)Time elapsed: 0.032 s
% 0.22/0.44  % (2460)------------------------------
% 0.22/0.44  % (2460)------------------------------
% 0.22/0.45  % (2446)Success in time 0.085 s
%------------------------------------------------------------------------------
