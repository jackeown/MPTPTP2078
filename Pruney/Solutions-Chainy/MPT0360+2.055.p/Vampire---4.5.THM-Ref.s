%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  71 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 181 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f287,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f287,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f285,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f285,plain,(
    ~ r2_hidden(sK3(sK1),sK1) ),
    inference(superposition,[],[f281,f40])).

fof(f40,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f281,plain,(
    ! [X6] : ~ r2_hidden(sK3(sK1),k3_xboole_0(X6,sK2)) ),
    inference(subsumption_resolution,[],[f276,f20])).

fof(f276,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK3(sK1),k3_xboole_0(X6,sK2))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f272,f21])).

fof(f272,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,sK2)) ) ),
    inference(superposition,[],[f100,f42])).

fof(f42,plain,(
    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f19,f27])).

fof(f19,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f100,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X5,k3_subset_1(sK0,sK2)))
      | ~ r2_hidden(X3,k3_xboole_0(X4,sK2)) ) ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f59,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k3_subset_1(sK0,sK2))
      | ~ r2_hidden(X2,k3_xboole_0(X3,sK2)) ) ),
    inference(resolution,[],[f57,f38])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,k3_subset_1(sK0,sK2)) ) ),
    inference(resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f56,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f35,f41])).

fof(f41,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f17,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (22176)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (22184)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (22184)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (22185)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (22185)Refutation not found, incomplete strategy% (22185)------------------------------
% 0.21/0.52  % (22185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22185)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22185)Memory used [KB]: 10618
% 0.21/0.52  % (22185)Time elapsed: 0.008 s
% 0.21/0.52  % (22185)------------------------------
% 0.21/0.52  % (22185)------------------------------
% 0.21/0.52  % (22177)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f287,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f285,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ~r2_hidden(sK3(sK1),sK1)),
% 0.21/0.53    inference(superposition,[],[f281,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f18,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    ( ! [X6] : (~r2_hidden(sK3(sK1),k3_xboole_0(X6,sK2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f276,f20])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ( ! [X6] : (~r2_hidden(sK3(sK1),k3_xboole_0(X6,sK2)) | k1_xboole_0 = sK1) )),
% 0.21/0.53    inference(resolution,[],[f272,f21])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k3_xboole_0(X1,sK2))) )),
% 0.21/0.53    inference(superposition,[],[f100,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f19,f27])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X5,k3_subset_1(sK0,sK2))) | ~r2_hidden(X3,k3_xboole_0(X4,sK2))) )),
% 0.21/0.53    inference(resolution,[],[f59,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k3_subset_1(sK0,sK2)) | ~r2_hidden(X2,k3_xboole_0(X3,sK2))) )),
% 0.21/0.53    inference(resolution,[],[f57,f38])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,k3_subset_1(sK0,sK2))) )),
% 0.21/0.53    inference(resolution,[],[f56,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.21/0.53    inference(superposition,[],[f35,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f17,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f23])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (22184)------------------------------
% 0.21/0.53  % (22184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22184)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (22184)Memory used [KB]: 1791
% 0.21/0.53  % (22184)Time elapsed: 0.101 s
% 0.21/0.53  % (22184)------------------------------
% 0.21/0.53  % (22184)------------------------------
% 0.21/0.53  % (22162)Success in time 0.171 s
%------------------------------------------------------------------------------
