%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:18 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 145 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  104 ( 239 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2020,plain,(
    $false ),
    inference(resolution,[],[f1933,f623])).

fof(f623,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(X0),k3_tarski(k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[],[f56,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) ),
    inference(definition_unfolding,[],[f40,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1933,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f1932,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f38,f38])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1932,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f1931,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f38,f38])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1931,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,k4_xboole_0(sK1,sK2))))) ),
    inference(forward_demodulation,[],[f1913,f59])).

fof(f1913,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))) ),
    inference(unit_resulting_resolution,[],[f1876,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1876,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f555,f1872])).

fof(f1872,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(sK1),X0) = k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f1821,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1821,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f1817,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1817,plain,(
    r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1812,f34])).

fof(f34,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f1812,plain,(
    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f623,f206])).

fof(f206,plain,(
    k1_zfmisc_1(u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f73,plain,(
    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f32,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(f555,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f547,f263])).

fof(f263,plain,(
    ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f152,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f152,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f134,f49])).

fof(f134,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f36,f73,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f547,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f277,f535])).

fof(f535,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f32,f52])).

fof(f277,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(backward_demodulation,[],[f270,f260])).

fof(f260,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f42])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f270,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(backward_demodulation,[],[f31,f261])).

fof(f261,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f32,f42])).

fof(f31,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:37:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (1774)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1775)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (1778)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (1777)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (1806)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (1796)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (1776)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1773)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (1783)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (1772)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (1798)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (1787)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (1793)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (1784)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1800)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (1785)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (1786)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (1802)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (1803)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (1780)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (1805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (1807)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (1801)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (1790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (1797)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (1804)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (1799)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (1795)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (1782)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (1779)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.18/0.65  % (1802)Refutation found. Thanks to Tanya!
% 2.18/0.65  % SZS status Theorem for theBenchmark
% 2.18/0.65  % SZS output start Proof for theBenchmark
% 2.18/0.65  fof(f2020,plain,(
% 2.18/0.65    $false),
% 2.18/0.65    inference(resolution,[],[f1933,f623])).
% 2.18/0.65  fof(f623,plain,(
% 2.18/0.65    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(k3_tarski(k2_tarski(X0,X1))))) )),
% 2.18/0.65    inference(superposition,[],[f56,f59])).
% 2.18/0.65  fof(f59,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1)))) )),
% 2.18/0.65    inference(definition_unfolding,[],[f40,f38,f38])).
% 2.18/0.65  fof(f38,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f11])).
% 2.18/0.65  fof(f11,axiom,(
% 2.18/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.18/0.65  fof(f40,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f12])).
% 2.18/0.65  fof(f12,axiom,(
% 2.18/0.65    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 2.18/0.65  fof(f56,plain,(
% 2.18/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 2.18/0.65    inference(definition_unfolding,[],[f35,f38])).
% 2.18/0.65  fof(f35,plain,(
% 2.18/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f10])).
% 2.18/0.65  fof(f10,axiom,(
% 2.18/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.18/0.65  fof(f1933,plain,(
% 2.18/0.65    ~r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK1,sK2))))),
% 2.18/0.65    inference(forward_demodulation,[],[f1932,f57])).
% 2.18/0.65  fof(f57,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 2.18/0.65    inference(definition_unfolding,[],[f37,f38,f38])).
% 2.18/0.65  fof(f37,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f1])).
% 2.18/0.65  fof(f1,axiom,(
% 2.18/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.18/0.65  fof(f1932,plain,(
% 2.18/0.65    ~r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,sK1))))),
% 2.18/0.65    inference(forward_demodulation,[],[f1931,f58])).
% 2.18/0.65  fof(f58,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 2.18/0.65    inference(definition_unfolding,[],[f39,f38,f38])).
% 2.18/0.65  fof(f39,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f6])).
% 2.18/0.65  fof(f6,axiom,(
% 2.18/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.18/0.65  fof(f1931,plain,(
% 2.18/0.65    ~r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,k4_xboole_0(sK1,sK2)))))),
% 2.18/0.65    inference(forward_demodulation,[],[f1913,f59])).
% 2.18/0.65  fof(f1913,plain,(
% 2.18/0.65    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))))),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f1876,f61])).
% 2.18/0.65  fof(f61,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.18/0.65    inference(definition_unfolding,[],[f53,f38])).
% 2.18/0.65  fof(f53,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f26])).
% 2.18/0.65  fof(f26,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.18/0.65    inference(ennf_transformation,[],[f7])).
% 2.18/0.65  fof(f7,axiom,(
% 2.18/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.18/0.65  fof(f1876,plain,(
% 2.18/0.65    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 2.18/0.65    inference(backward_demodulation,[],[f555,f1872])).
% 2.18/0.65  fof(f1872,plain,(
% 2.18/0.65    ( ! [X0] : (k4_xboole_0(k3_tarski(sK1),X0) = k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0)) )),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f1821,f52])).
% 2.18/0.65  fof(f52,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f25])).
% 2.18/0.65  fof(f25,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.65    inference(ennf_transformation,[],[f14])).
% 2.18/0.65  fof(f14,axiom,(
% 2.18/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.18/0.65  fof(f1821,plain,(
% 2.18/0.65    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f1817,f49])).
% 2.18/0.65  fof(f49,plain,(
% 2.18/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f16,axiom,(
% 2.18/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.65  fof(f1817,plain,(
% 2.18/0.65    r1_tarski(k3_tarski(sK1),u1_struct_0(sK0))),
% 2.18/0.65    inference(forward_demodulation,[],[f1812,f34])).
% 2.18/0.65  fof(f34,plain,(
% 2.18/0.65    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.18/0.65    inference(cnf_transformation,[],[f13])).
% 2.18/0.65  fof(f13,axiom,(
% 2.18/0.65    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 2.18/0.65  fof(f1812,plain,(
% 2.18/0.65    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.18/0.65    inference(superposition,[],[f623,f206])).
% 2.18/0.65  fof(f206,plain,(
% 2.18/0.65    k1_zfmisc_1(u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f73,f65])).
% 2.18/0.65  fof(f65,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.18/0.65    inference(forward_demodulation,[],[f60,f58])).
% 2.18/0.65  fof(f60,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = X1) )),
% 2.18/0.65    inference(definition_unfolding,[],[f41,f38])).
% 2.18/0.65  fof(f41,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 2.18/0.65    inference(cnf_transformation,[],[f21])).
% 2.18/0.65  fof(f21,plain,(
% 2.18/0.65    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.18/0.65    inference(ennf_transformation,[],[f9])).
% 2.18/0.65  fof(f9,axiom,(
% 2.18/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 2.18/0.65  fof(f73,plain,(
% 2.18/0.65    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f32,f50])).
% 2.18/0.65  fof(f50,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f32,plain,(
% 2.18/0.65    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  fof(f20,plain,(
% 2.18/0.65    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 2.18/0.65    inference(ennf_transformation,[],[f19])).
% 2.18/0.65  fof(f19,negated_conjecture,(
% 2.18/0.65    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 2.18/0.65    inference(negated_conjecture,[],[f18])).
% 2.18/0.65  fof(f18,conjecture,(
% 2.18/0.65    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).
% 2.18/0.65  fof(f555,plain,(
% 2.18/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 2.18/0.65    inference(forward_demodulation,[],[f547,f263])).
% 2.18/0.65  fof(f263,plain,(
% 2.18/0.65    ( ! [X0] : (k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) )),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f152,f42])).
% 2.18/0.65  fof(f42,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f22])).
% 2.18/0.65  fof(f22,plain,(
% 2.18/0.65    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.18/0.65    inference(ennf_transformation,[],[f15])).
% 2.18/0.65  fof(f15,axiom,(
% 2.18/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 2.18/0.65  fof(f152,plain,(
% 2.18/0.65    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f134,f49])).
% 2.18/0.65  fof(f134,plain,(
% 2.18/0.65    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f36,f73,f55])).
% 2.18/0.65  fof(f55,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f29])).
% 2.18/0.65  fof(f29,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.18/0.65    inference(flattening,[],[f28])).
% 2.18/0.65  fof(f28,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.18/0.65    inference(ennf_transformation,[],[f4])).
% 2.18/0.65  fof(f4,axiom,(
% 2.18/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.18/0.65  fof(f36,plain,(
% 2.18/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f5])).
% 2.18/0.65  fof(f5,axiom,(
% 2.18/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.18/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.18/0.65  fof(f547,plain,(
% 2.18/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 2.18/0.65    inference(backward_demodulation,[],[f277,f535])).
% 2.18/0.65  fof(f535,plain,(
% 2.18/0.65    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0)) )),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f32,f52])).
% 2.18/0.65  fof(f277,plain,(
% 2.18/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.18/0.65    inference(backward_demodulation,[],[f270,f260])).
% 2.18/0.65  fof(f260,plain,(
% 2.18/0.65    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f30,f42])).
% 2.18/0.65  fof(f30,plain,(
% 2.18/0.65    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  fof(f270,plain,(
% 2.18/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.18/0.65    inference(backward_demodulation,[],[f31,f261])).
% 2.18/0.65  fof(f261,plain,(
% 2.18/0.65    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 2.18/0.65    inference(unit_resulting_resolution,[],[f32,f42])).
% 2.18/0.65  fof(f31,plain,(
% 2.18/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  % SZS output end Proof for theBenchmark
% 2.18/0.65  % (1802)------------------------------
% 2.18/0.65  % (1802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.65  % (1802)Termination reason: Refutation
% 2.18/0.65  
% 2.18/0.65  % (1802)Memory used [KB]: 7675
% 2.18/0.65  % (1802)Time elapsed: 0.242 s
% 2.18/0.65  % (1802)------------------------------
% 2.18/0.65  % (1802)------------------------------
% 2.18/0.66  % (1771)Success in time 0.291 s
%------------------------------------------------------------------------------
