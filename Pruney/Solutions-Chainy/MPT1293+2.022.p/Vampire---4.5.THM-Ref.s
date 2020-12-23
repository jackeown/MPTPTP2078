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
% DateTime   : Thu Dec  3 13:13:20 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  109 ( 221 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f970,plain,(
    $false ),
    inference(resolution,[],[f969,f264])).

fof(f264,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(X1),k3_tarski(k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f225,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f225,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X1,X0))) ),
    inference(resolution,[],[f57,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f57,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(k4_xboole_0(X11,k3_tarski(X9)),k3_tarski(X10))
      | r1_tarski(X11,k3_tarski(k2_xboole_0(X9,X10))) ) ),
    inference(superposition,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f969,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f968,f108])).

fof(f108,plain,(
    ! [X2,X3] : k3_tarski(k2_xboole_0(X2,X3)) = k3_tarski(k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f48,f31])).

fof(f48,plain,(
    ! [X2,X3] : k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f31,f29])).

fof(f968,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f967,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f967,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f964,f31])).

fof(f964,plain,(
    ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f955,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f955,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f710,f942])).

fof(f942,plain,(
    ! [X65] : k4_xboole_0(k3_tarski(sK1),X65) = k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X65) ),
    inference(forward_demodulation,[],[f940,f27])).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f940,plain,(
    ! [X65] : k4_xboole_0(k3_tarski(sK1),X65) = k7_subset_1(k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))),k3_tarski(sK1),X65) ),
    inference(resolution,[],[f208,f41])).

fof(f41,plain,(
    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f208,plain,(
    ! [X24,X23,X22] :
      ( ~ r1_tarski(X22,X24)
      | k4_xboole_0(k3_tarski(X22),X23) = k7_subset_1(k3_tarski(X24),k3_tarski(X22),X23) ) ),
    inference(resolution,[],[f82,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f82,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k4_xboole_0(X3,X4) = k7_subset_1(X2,X3,X4) ) ),
    inference(resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f710,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f84,f688])).

fof(f688,plain,(
    ! [X2] : k3_tarski(k4_xboole_0(sK1,X2)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X2)) ),
    inference(resolution,[],[f663,f28])).

fof(f663,plain,(
    ! [X14] :
      ( ~ r1_tarski(X14,sK1)
      | k3_tarski(X14) = k5_setfam_1(u1_struct_0(sK0),X14) ) ),
    inference(resolution,[],[f161,f41])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X2)
      | k3_tarski(X0) = k5_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
      | k3_tarski(X0) = k5_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f84,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f74,f81])).

fof(f81,plain,(
    ! [X1] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X1) = k4_xboole_0(sK1,X1) ),
    inference(resolution,[],[f36,f26])).

fof(f74,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(backward_demodulation,[],[f72,f70])).

fof(f70,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(resolution,[],[f33,f26])).

fof(f72,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(backward_demodulation,[],[f25,f69])).

fof(f69,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (26700)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.46  % (26708)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.48  % (26698)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (26693)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (26713)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (26695)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (26694)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (26701)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (26697)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (26704)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (26705)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (26711)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (26696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.27/0.51  % (26706)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.27/0.51  % (26691)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.27/0.52  % (26703)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.27/0.52  % (26712)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.27/0.52  % (26709)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.27/0.52  % (26692)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.27/0.52  % (26699)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.37/0.53  % (26702)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.37/0.53  % (26714)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.37/0.54  % (26707)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.37/0.54  % (26710)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.37/0.60  % (26703)Refutation found. Thanks to Tanya!
% 1.37/0.60  % SZS status Theorem for theBenchmark
% 2.13/0.63  % SZS output start Proof for theBenchmark
% 2.13/0.63  fof(f970,plain,(
% 2.13/0.63    $false),
% 2.13/0.63    inference(resolution,[],[f969,f264])).
% 2.13/0.63  fof(f264,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(k3_tarski(X1),k3_tarski(k2_xboole_0(X1,X0)))) )),
% 2.13/0.63    inference(superposition,[],[f225,f29])).
% 2.13/0.63  fof(f29,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f1])).
% 2.13/0.63  fof(f1,axiom,(
% 2.13/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.13/0.63  fof(f225,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X1,X0)))) )),
% 2.13/0.63    inference(resolution,[],[f57,f28])).
% 2.13/0.63  fof(f28,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f3])).
% 2.13/0.63  fof(f3,axiom,(
% 2.13/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.13/0.63  fof(f57,plain,(
% 2.13/0.63    ( ! [X10,X11,X9] : (~r1_tarski(k4_xboole_0(X11,k3_tarski(X9)),k3_tarski(X10)) | r1_tarski(X11,k3_tarski(k2_xboole_0(X9,X10)))) )),
% 2.13/0.63    inference(superposition,[],[f38,f31])).
% 2.13/0.63  fof(f31,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f8])).
% 2.13/0.63  fof(f8,axiom,(
% 2.13/0.63    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 2.13/0.63  fof(f38,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f21])).
% 2.13/0.63  fof(f21,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.63    inference(ennf_transformation,[],[f6])).
% 2.13/0.63  fof(f6,axiom,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.13/0.63  fof(f969,plain,(
% 2.13/0.63    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))),
% 2.13/0.63    inference(forward_demodulation,[],[f968,f108])).
% 2.13/0.63  fof(f108,plain,(
% 2.13/0.63    ( ! [X2,X3] : (k3_tarski(k2_xboole_0(X2,X3)) = k3_tarski(k2_xboole_0(X3,X2))) )),
% 2.13/0.63    inference(superposition,[],[f48,f31])).
% 2.13/0.63  fof(f48,plain,(
% 2.13/0.63    ( ! [X2,X3] : (k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))) )),
% 2.13/0.63    inference(superposition,[],[f31,f29])).
% 2.13/0.63  fof(f968,plain,(
% 2.13/0.63    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))),
% 2.13/0.63    inference(forward_demodulation,[],[f967,f30])).
% 2.13/0.63  fof(f30,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f4])).
% 2.13/0.63  fof(f4,axiom,(
% 2.13/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.13/0.63  fof(f967,plain,(
% 2.13/0.63    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 2.13/0.63    inference(forward_demodulation,[],[f964,f31])).
% 2.13/0.63  fof(f964,plain,(
% 2.13/0.63    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))),
% 2.13/0.63    inference(resolution,[],[f955,f37])).
% 2.13/0.63  fof(f37,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f20])).
% 2.13/0.63  fof(f20,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.63    inference(ennf_transformation,[],[f5])).
% 2.13/0.63  fof(f5,axiom,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.13/0.63  fof(f955,plain,(
% 2.13/0.63    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 2.13/0.63    inference(backward_demodulation,[],[f710,f942])).
% 2.13/0.63  fof(f942,plain,(
% 2.13/0.63    ( ! [X65] : (k4_xboole_0(k3_tarski(sK1),X65) = k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X65)) )),
% 2.13/0.63    inference(forward_demodulation,[],[f940,f27])).
% 2.13/0.63  fof(f27,plain,(
% 2.13/0.63    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.13/0.63    inference(cnf_transformation,[],[f9])).
% 2.13/0.63  fof(f9,axiom,(
% 2.13/0.63    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 2.13/0.63  fof(f940,plain,(
% 2.13/0.63    ( ! [X65] : (k4_xboole_0(k3_tarski(sK1),X65) = k7_subset_1(k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))),k3_tarski(sK1),X65)) )),
% 2.13/0.63    inference(resolution,[],[f208,f41])).
% 2.13/0.63  fof(f41,plain,(
% 2.13/0.63    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.63    inference(resolution,[],[f35,f26])).
% 2.13/0.63  fof(f26,plain,(
% 2.13/0.63    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.63    inference(cnf_transformation,[],[f16])).
% 2.13/0.63  fof(f16,plain,(
% 2.13/0.63    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.13/0.63    inference(ennf_transformation,[],[f15])).
% 2.13/0.63  fof(f15,plain,(
% 2.13/0.63    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))))),
% 2.13/0.63    inference(pure_predicate_removal,[],[f14])).
% 2.13/0.63  fof(f14,negated_conjecture,(
% 2.13/0.63    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 2.13/0.63    inference(negated_conjecture,[],[f13])).
% 2.13/0.63  fof(f13,conjecture,(
% 2.13/0.63    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).
% 2.13/0.63  fof(f35,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f12])).
% 2.13/0.63  fof(f12,axiom,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.13/0.63  fof(f208,plain,(
% 2.13/0.63    ( ! [X24,X23,X22] : (~r1_tarski(X22,X24) | k4_xboole_0(k3_tarski(X22),X23) = k7_subset_1(k3_tarski(X24),k3_tarski(X22),X23)) )),
% 2.13/0.63    inference(resolution,[],[f82,f32])).
% 2.13/0.63  fof(f32,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f17])).
% 2.13/0.63  fof(f17,plain,(
% 2.13/0.63    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 2.13/0.63    inference(ennf_transformation,[],[f7])).
% 2.13/0.63  fof(f7,axiom,(
% 2.13/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 2.13/0.63  fof(f82,plain,(
% 2.13/0.63    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | k4_xboole_0(X3,X4) = k7_subset_1(X2,X3,X4)) )),
% 2.13/0.63    inference(resolution,[],[f36,f34])).
% 2.13/0.63  fof(f34,plain,(
% 2.13/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f12])).
% 2.13/0.63  fof(f36,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f19])).
% 2.13/0.63  fof(f19,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f10])).
% 2.13/0.63  fof(f10,axiom,(
% 2.13/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.13/0.63  fof(f710,plain,(
% 2.13/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 2.13/0.63    inference(backward_demodulation,[],[f84,f688])).
% 2.13/0.63  fof(f688,plain,(
% 2.13/0.63    ( ! [X2] : (k3_tarski(k4_xboole_0(sK1,X2)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X2))) )),
% 2.13/0.63    inference(resolution,[],[f663,f28])).
% 2.13/0.63  fof(f663,plain,(
% 2.13/0.63    ( ! [X14] : (~r1_tarski(X14,sK1) | k3_tarski(X14) = k5_setfam_1(u1_struct_0(sK0),X14)) )),
% 2.13/0.63    inference(resolution,[],[f161,f41])).
% 2.13/0.63  fof(f161,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X2) | k3_tarski(X0) = k5_setfam_1(X1,X0)) )),
% 2.13/0.63    inference(resolution,[],[f71,f39])).
% 2.13/0.63  fof(f39,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f23,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.13/0.63    inference(flattening,[],[f22])).
% 2.13/0.63  fof(f22,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.13/0.63    inference(ennf_transformation,[],[f2])).
% 2.13/0.63  fof(f2,axiom,(
% 2.13/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.13/0.63  fof(f71,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k1_zfmisc_1(X1)) | k3_tarski(X0) = k5_setfam_1(X1,X0)) )),
% 2.13/0.63    inference(resolution,[],[f33,f34])).
% 2.13/0.63  fof(f33,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f18])).
% 2.13/0.63  fof(f18,plain,(
% 2.13/0.63    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.63    inference(ennf_transformation,[],[f11])).
% 2.13/0.63  fof(f11,axiom,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 2.13/0.63  fof(f84,plain,(
% 2.13/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 2.13/0.63    inference(backward_demodulation,[],[f74,f81])).
% 2.13/0.63  fof(f81,plain,(
% 2.13/0.63    ( ! [X1] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X1) = k4_xboole_0(sK1,X1)) )),
% 2.13/0.63    inference(resolution,[],[f36,f26])).
% 2.13/0.63  fof(f74,plain,(
% 2.13/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.13/0.63    inference(backward_demodulation,[],[f72,f70])).
% 2.13/0.63  fof(f70,plain,(
% 2.13/0.63    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 2.13/0.63    inference(resolution,[],[f33,f26])).
% 2.13/0.63  fof(f72,plain,(
% 2.13/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.13/0.63    inference(backward_demodulation,[],[f25,f69])).
% 2.13/0.63  fof(f69,plain,(
% 2.13/0.63    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)),
% 2.13/0.63    inference(resolution,[],[f33,f24])).
% 2.13/0.63  fof(f24,plain,(
% 2.13/0.63    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.63    inference(cnf_transformation,[],[f16])).
% 2.13/0.63  fof(f25,plain,(
% 2.13/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.13/0.63    inference(cnf_transformation,[],[f16])).
% 2.13/0.63  % SZS output end Proof for theBenchmark
% 2.13/0.63  % (26703)------------------------------
% 2.13/0.63  % (26703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.63  % (26703)Termination reason: Refutation
% 2.13/0.63  
% 2.13/0.63  % (26703)Memory used [KB]: 11641
% 2.13/0.63  % (26703)Time elapsed: 0.212 s
% 2.13/0.63  % (26703)------------------------------
% 2.13/0.63  % (26703)------------------------------
% 2.13/0.63  % (26690)Success in time 0.275 s
%------------------------------------------------------------------------------
