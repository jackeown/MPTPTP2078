%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:06 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  89 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 465 expanded)
%              Number of equality atoms :   22 ( 118 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,(
    r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f18,f14,f16,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).

fof(f14,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ~ r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(backward_demodulation,[],[f44,f40])).

fof(f40,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f12,f26,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f26,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f17,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f17,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ~ r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK0))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f41,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f12,f26,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ~ r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f17,f24,f25,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f11,f13])).

fof(f13,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f7])).

fof(f11,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ~ v2_tops_2(sK2,sK1) ),
    inference(backward_demodulation,[],[f15,f13])).

fof(f15,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:13:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (4530)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (4536)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (4534)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.52  % (4553)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.52  % (4534)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.52  % SZS output start Proof for theBenchmark
% 1.21/0.52  fof(f73,plain,(
% 1.21/0.52    $false),
% 1.21/0.52    inference(resolution,[],[f52,f34])).
% 1.21/0.52  fof(f34,plain,(
% 1.21/0.52    r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f18,f14,f16,f20])).
% 1.21/0.52  fof(f20,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f8])).
% 1.21/0.52  fof(f8,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f3])).
% 1.21/0.52  fof(f3,axiom,(
% 1.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).
% 1.21/0.52  fof(f16,plain,(
% 1.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f7,plain,(
% 1.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.21/0.52    inference(flattening,[],[f6])).
% 1.21/0.52  fof(f6,plain,(
% 1.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tops_2(X3,X1) & (v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f5])).
% 1.21/0.52  fof(f5,negated_conjecture,(
% 1.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 1.21/0.52    inference(negated_conjecture,[],[f4])).
% 1.21/0.52  fof(f4,conjecture,(
% 1.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    v2_tops_2(sK2,sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f18,plain,(
% 1.21/0.52    l1_pre_topc(sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f52,plain,(
% 1.21/0.52    ~r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.21/0.52    inference(backward_demodulation,[],[f44,f40])).
% 1.21/0.52  fof(f40,plain,(
% 1.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f12,f26,f21])).
% 1.21/0.52  fof(f21,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f9])).
% 1.21/0.52  fof(f9,plain,(
% 1.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.52    inference(ennf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f17,f23])).
% 1.21/0.52  fof(f23,plain,(
% 1.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f10])).
% 1.21/0.52  fof(f10,plain,(
% 1.21/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f1])).
% 1.21/0.52  fof(f1,axiom,(
% 1.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.21/0.52  fof(f17,plain,(
% 1.21/0.52    l1_pre_topc(sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f12,plain,(
% 1.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f44,plain,(
% 1.21/0.52    ~r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK0)))),
% 1.21/0.52    inference(backward_demodulation,[],[f37,f41])).
% 1.21/0.52  fof(f41,plain,(
% 1.21/0.52    u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f12,f26,f22])).
% 1.21/0.52  fof(f22,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 1.21/0.52    inference(cnf_transformation,[],[f9])).
% 1.21/0.52  fof(f37,plain,(
% 1.21/0.52    ~r1_tarski(sK2,k7_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f17,f24,f25,f19])).
% 1.21/0.52  fof(f19,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f8])).
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.21/0.52    inference(forward_demodulation,[],[f11,f13])).
% 1.21/0.52  fof(f13,plain,(
% 1.21/0.52    sK2 = sK3),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f11,plain,(
% 1.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    ~v2_tops_2(sK2,sK1)),
% 1.21/0.52    inference(backward_demodulation,[],[f15,f13])).
% 1.21/0.52  fof(f15,plain,(
% 1.21/0.52    ~v2_tops_2(sK3,sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (4534)------------------------------
% 1.21/0.52  % (4534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (4534)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (4534)Memory used [KB]: 6268
% 1.21/0.52  % (4534)Time elapsed: 0.108 s
% 1.21/0.52  % (4534)------------------------------
% 1.21/0.52  % (4534)------------------------------
% 1.21/0.52  % (4535)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.52  % (4545)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.52  % (4533)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.52  % (4530)Refutation not found, incomplete strategy% (4530)------------------------------
% 1.21/0.52  % (4530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (4545)Refutation not found, incomplete strategy% (4545)------------------------------
% 1.21/0.53  % (4545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (4545)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (4545)Memory used [KB]: 6140
% 1.21/0.53  % (4545)Time elapsed: 0.074 s
% 1.21/0.53  % (4545)------------------------------
% 1.21/0.53  % (4545)------------------------------
% 1.21/0.53  % (4530)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (4530)Memory used [KB]: 1791
% 1.21/0.53  % (4530)Time elapsed: 0.093 s
% 1.21/0.53  % (4530)------------------------------
% 1.21/0.53  % (4530)------------------------------
% 1.21/0.53  % (4537)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.53  % (4538)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.53  % (4549)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.21/0.54  % (4531)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.54  % (4559)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.21/0.54  % (4542)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (4557)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.54  % (4556)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (4529)Success in time 0.172 s
%------------------------------------------------------------------------------
