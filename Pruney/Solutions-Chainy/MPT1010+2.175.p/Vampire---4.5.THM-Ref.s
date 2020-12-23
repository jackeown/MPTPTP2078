%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:15 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 384 expanded)
%              Number of leaves         :   10 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  140 (1062 expanded)
%              Number of equality atoms :   50 ( 377 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f355,f411])).

fof(f411,plain,(
    ! [X0,X1] : r2_hidden(k1_mcart_1(X0),X1) ),
    inference(subsumption_resolution,[],[f346,f324])).

fof(f324,plain,(
    ! [X0] : r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK1))) ),
    inference(backward_demodulation,[],[f112,f283])).

fof(f283,plain,(
    ! [X0] : k1_mcart_1(k2_mcart_1(sK1)) = X0 ),
    inference(unit_resulting_resolution,[],[f171,f218])).

fof(f218,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | k1_mcart_1(k2_mcart_1(X2)) = X0 ) ),
    inference(superposition,[],[f120,f126])).

fof(f126,plain,(
    ! [X9] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X9) ),
    inference(forward_demodulation,[],[f123,f79])).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f123,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(X7,X8,k1_xboole_0),X9) ),
    inference(superposition,[],[f70,f80])).

fof(f80,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f120,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(X11,k2_zfmisc_1(X13,k2_zfmisc_1(k1_enumset1(X12,X12,X12),X14)))
      | k1_mcart_1(k2_mcart_1(X11)) = X12 ) ),
    inference(resolution,[],[f72,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f171,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f113,f144])).

fof(f144,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f33,f36,f107,f69,f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f35,f67])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f69,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f34,f67])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f99,plain,(
    ~ sP7(k1_funct_1(sK3,sK2),sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f37,f37,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f113,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f85,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,(
    ! [X3,X1] : sP7(X3,X1,X3) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f112,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(unit_resulting_resolution,[],[f84,f83])).

fof(f84,plain,(
    ! [X0,X3] : sP7(X3,X3,X0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f346,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK1)))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(backward_demodulation,[],[f49,f283])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f355,plain,(
    ~ r2_hidden(k1_mcart_1(k2_mcart_1(sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f151,f283])).

fof(f151,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f107,f144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (31224)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (31223)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (31222)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (31215)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31231)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (31216)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (31209)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (31238)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (31210)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (31220)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (31238)Refutation not found, incomplete strategy% (31238)------------------------------
% 0.21/0.54  % (31238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31238)Memory used [KB]: 1663
% 0.21/0.54  % (31238)Time elapsed: 0.126 s
% 0.21/0.54  % (31238)------------------------------
% 0.21/0.54  % (31238)------------------------------
% 0.21/0.55  % (31211)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (31232)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (31212)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (31214)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (31219)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (31218)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (31217)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (31226)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (31213)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (31237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (31225)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (31225)Refutation not found, incomplete strategy% (31225)------------------------------
% 0.21/0.57  % (31225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (31225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (31225)Memory used [KB]: 10746
% 0.21/0.57  % (31225)Time elapsed: 0.166 s
% 0.21/0.57  % (31225)------------------------------
% 0.21/0.57  % (31225)------------------------------
% 0.21/0.58  % (31228)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.58  % (31234)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.58  % (31236)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.58  % (31236)Refutation not found, incomplete strategy% (31236)------------------------------
% 0.21/0.58  % (31236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (31236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (31236)Memory used [KB]: 6268
% 0.21/0.58  % (31236)Time elapsed: 0.181 s
% 0.21/0.58  % (31236)------------------------------
% 0.21/0.58  % (31236)------------------------------
% 0.21/0.58  % (31229)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.59  % (31233)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.59  % (31233)Refutation not found, incomplete strategy% (31233)------------------------------
% 0.21/0.59  % (31233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (31233)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (31233)Memory used [KB]: 10746
% 0.21/0.59  % (31233)Time elapsed: 0.179 s
% 0.21/0.59  % (31233)------------------------------
% 0.21/0.59  % (31233)------------------------------
% 0.21/0.60  % (31230)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.60  % (31235)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.61  % (31221)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.86/0.62  % (31227)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.86/0.62  % (31228)Refutation found. Thanks to Tanya!
% 1.86/0.62  % SZS status Theorem for theBenchmark
% 1.86/0.62  % SZS output start Proof for theBenchmark
% 1.86/0.62  fof(f412,plain,(
% 1.86/0.62    $false),
% 1.86/0.62    inference(subsumption_resolution,[],[f355,f411])).
% 1.86/0.62  fof(f411,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.86/0.62    inference(subsumption_resolution,[],[f346,f324])).
% 1.86/0.62  fof(f324,plain,(
% 1.86/0.62    ( ! [X0] : (r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK1)))) )),
% 1.86/0.62    inference(backward_demodulation,[],[f112,f283])).
% 1.86/0.62  fof(f283,plain,(
% 1.86/0.62    ( ! [X0] : (k1_mcart_1(k2_mcart_1(sK1)) = X0) )),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f171,f218])).
% 1.86/0.62  fof(f218,plain,(
% 1.86/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k1_xboole_0) | k1_mcart_1(k2_mcart_1(X2)) = X0) )),
% 1.86/0.62    inference(superposition,[],[f120,f126])).
% 1.86/0.62  fof(f126,plain,(
% 1.86/0.62    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X9)) )),
% 1.86/0.62    inference(forward_demodulation,[],[f123,f79])).
% 1.86/0.62  fof(f79,plain,(
% 1.86/0.62    ( ! [X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0)) )),
% 1.86/0.62    inference(equality_resolution,[],[f55])).
% 1.86/0.62  fof(f55,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k1_xboole_0 != X2) )),
% 1.86/0.62    inference(cnf_transformation,[],[f19])).
% 1.86/0.62  fof(f19,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.86/0.62  fof(f123,plain,(
% 1.86/0.62    ( ! [X8,X7,X9] : (k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(X7,X8,k1_xboole_0),X9)) )),
% 1.86/0.62    inference(superposition,[],[f70,f80])).
% 1.86/0.62  fof(f80,plain,(
% 1.86/0.62    ( ! [X2,X0] : (k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2)) )),
% 1.86/0.62    inference(equality_resolution,[],[f54])).
% 1.86/0.62  fof(f54,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.86/0.62    inference(cnf_transformation,[],[f19])).
% 1.86/0.62  fof(f70,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 1.86/0.62    inference(definition_unfolding,[],[f46,f45])).
% 1.86/0.62  fof(f45,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f20])).
% 1.86/0.62  fof(f20,axiom,(
% 1.86/0.62    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).
% 1.86/0.62  fof(f46,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f16])).
% 1.86/0.62  fof(f16,axiom,(
% 1.86/0.62    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.86/0.62  fof(f120,plain,(
% 1.86/0.62    ( ! [X14,X12,X13,X11] : (~r2_hidden(X11,k2_zfmisc_1(X13,k2_zfmisc_1(k1_enumset1(X12,X12,X12),X14))) | k1_mcart_1(k2_mcart_1(X11)) = X12) )),
% 1.86/0.62    inference(resolution,[],[f72,f50])).
% 1.86/0.62  fof(f50,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f31])).
% 1.86/0.62  fof(f31,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.86/0.62    inference(ennf_transformation,[],[f17])).
% 1.86/0.62  fof(f17,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.86/0.62  fof(f72,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.86/0.62    inference(definition_unfolding,[],[f47,f67])).
% 1.86/0.62  fof(f67,plain,(
% 1.86/0.62    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.86/0.62    inference(definition_unfolding,[],[f51,f66])).
% 1.86/0.62  fof(f66,plain,(
% 1.86/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f6])).
% 1.86/0.62  fof(f6,axiom,(
% 1.86/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.86/0.62  fof(f51,plain,(
% 1.86/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f5])).
% 1.86/0.62  fof(f5,axiom,(
% 1.86/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.86/0.62  fof(f47,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.86/0.62    inference(cnf_transformation,[],[f30])).
% 1.86/0.62  fof(f30,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.86/0.62    inference(ennf_transformation,[],[f18])).
% 1.86/0.62  fof(f18,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.86/0.62  fof(f171,plain,(
% 1.86/0.62    r2_hidden(sK1,k1_xboole_0)),
% 1.86/0.62    inference(superposition,[],[f113,f144])).
% 1.86/0.62  fof(f144,plain,(
% 1.86/0.62    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f33,f36,f107,f69,f68,f38])).
% 1.86/0.62  fof(f38,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f27])).
% 1.86/0.62  fof(f27,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.86/0.62    inference(flattening,[],[f26])).
% 1.86/0.62  fof(f26,plain,(
% 1.86/0.62    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.86/0.62    inference(ennf_transformation,[],[f21])).
% 1.86/0.62  fof(f21,axiom,(
% 1.86/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.86/0.62  fof(f68,plain,(
% 1.86/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 1.86/0.62    inference(definition_unfolding,[],[f35,f67])).
% 1.86/0.62  fof(f35,plain,(
% 1.86/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.86/0.62    inference(cnf_transformation,[],[f25])).
% 1.86/0.62  fof(f25,plain,(
% 1.86/0.62    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.86/0.62    inference(flattening,[],[f24])).
% 1.86/0.62  fof(f24,plain,(
% 1.86/0.62    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.86/0.62    inference(ennf_transformation,[],[f23])).
% 1.86/0.62  fof(f23,negated_conjecture,(
% 1.86/0.62    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.86/0.62    inference(negated_conjecture,[],[f22])).
% 1.86/0.62  fof(f22,conjecture,(
% 1.86/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.86/0.62  fof(f69,plain,(
% 1.86/0.62    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 1.86/0.62    inference(definition_unfolding,[],[f34,f67])).
% 1.86/0.62  fof(f34,plain,(
% 1.86/0.62    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.86/0.62    inference(cnf_transformation,[],[f25])).
% 1.86/0.62  fof(f107,plain,(
% 1.86/0.62    ~r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f99,f82])).
% 1.86/0.62  fof(f82,plain,(
% 1.86/0.62    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,k1_enumset1(X0,X0,X1))) )),
% 1.86/0.62    inference(equality_resolution,[],[f75])).
% 1.86/0.62  fof(f75,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.86/0.62    inference(definition_unfolding,[],[f63,f66])).
% 1.86/0.62  fof(f63,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.86/0.62    inference(cnf_transformation,[],[f4])).
% 1.86/0.62  fof(f4,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.86/0.62  fof(f99,plain,(
% 1.86/0.62    ~sP7(k1_funct_1(sK3,sK2),sK1,sK1)),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f37,f37,f61])).
% 1.86/0.62  fof(f61,plain,(
% 1.86/0.62    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.86/0.62    inference(cnf_transformation,[],[f4])).
% 1.86/0.62  fof(f37,plain,(
% 1.86/0.62    sK1 != k1_funct_1(sK3,sK2)),
% 1.86/0.62    inference(cnf_transformation,[],[f25])).
% 1.86/0.62  fof(f36,plain,(
% 1.86/0.62    r2_hidden(sK2,sK0)),
% 1.86/0.62    inference(cnf_transformation,[],[f25])).
% 1.86/0.62  fof(f33,plain,(
% 1.86/0.62    v1_funct_1(sK3)),
% 1.86/0.62    inference(cnf_transformation,[],[f25])).
% 1.86/0.62  fof(f113,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f85,f83])).
% 1.86/0.62  fof(f83,plain,(
% 1.86/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_enumset1(X0,X0,X1)) | ~sP7(X3,X1,X0)) )),
% 1.86/0.62    inference(equality_resolution,[],[f76])).
% 1.86/0.62  fof(f76,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.86/0.62    inference(definition_unfolding,[],[f62,f66])).
% 1.86/0.62  fof(f62,plain,(
% 1.86/0.62    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.86/0.62    inference(cnf_transformation,[],[f4])).
% 1.86/0.62  fof(f85,plain,(
% 1.86/0.62    ( ! [X3,X1] : (sP7(X3,X1,X3)) )),
% 1.86/0.62    inference(equality_resolution,[],[f59])).
% 1.86/0.62  fof(f59,plain,(
% 1.86/0.62    ( ! [X0,X3,X1] : (X0 != X3 | sP7(X3,X1,X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f4])).
% 1.86/0.62  fof(f112,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f84,f83])).
% 1.86/0.62  fof(f84,plain,(
% 1.86/0.62    ( ! [X0,X3] : (sP7(X3,X3,X0)) )),
% 1.86/0.62    inference(equality_resolution,[],[f60])).
% 1.86/0.62  fof(f60,plain,(
% 1.86/0.62    ( ! [X0,X3,X1] : (X1 != X3 | sP7(X3,X1,X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f4])).
% 1.86/0.62  fof(f346,plain,(
% 1.86/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK1))) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.86/0.62    inference(backward_demodulation,[],[f49,f283])).
% 1.86/0.62  fof(f49,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f31])).
% 1.86/0.62  fof(f355,plain,(
% 1.86/0.62    ~r2_hidden(k1_mcart_1(k2_mcart_1(sK1)),k1_xboole_0)),
% 1.86/0.62    inference(backward_demodulation,[],[f151,f283])).
% 1.86/0.62  fof(f151,plain,(
% 1.86/0.62    ~r2_hidden(k1_funct_1(sK3,sK2),k1_xboole_0)),
% 1.86/0.62    inference(backward_demodulation,[],[f107,f144])).
% 1.86/0.62  % SZS output end Proof for theBenchmark
% 1.86/0.62  % (31228)------------------------------
% 1.86/0.62  % (31228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.62  % (31228)Termination reason: Refutation
% 1.86/0.62  
% 1.86/0.62  % (31228)Memory used [KB]: 1918
% 1.86/0.62  % (31228)Time elapsed: 0.202 s
% 1.86/0.62  % (31228)------------------------------
% 1.86/0.62  % (31228)------------------------------
% 1.86/0.62  % (31208)Success in time 0.263 s
%------------------------------------------------------------------------------
