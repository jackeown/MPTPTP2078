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
% DateTime   : Thu Dec  3 12:44:42 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 885 expanded)
%              Number of leaves         :   13 ( 230 expanded)
%              Depth                    :   21
%              Number of atoms          :  171 (1870 expanded)
%              Number of equality atoms :   58 ( 625 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1105,plain,(
    $false ),
    inference(resolution,[],[f1061,f1055])).

fof(f1055,plain,(
    ~ r2_hidden(sK5(k5_xboole_0(sK0,sK0),sK0),sK0) ),
    inference(forward_demodulation,[],[f1043,f987])).

fof(f987,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f979])).

fof(f979,plain,
    ( sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f978,f222])).

fof(f222,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f174,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f174,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(superposition,[],[f144,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f144,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f119,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f119,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f113,f51])).

fof(f113,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f99,f59])).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f99,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f93,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f31,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f978,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f972])).

fof(f972,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK0)
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f955,f223])).

fof(f223,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f174,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f955,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | sK0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f935])).

fof(f935,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1)
      | sK0 = sK1
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f744,f198])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK0,sK1))
      | sK0 = sK1
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f193,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f193,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f89,f173])).

fof(f173,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f90,f144])).

fof(f90,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f31,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f89,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f71,f72])).

fof(f72,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f69,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f71,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f29,f69])).

fof(f29,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f744,plain,(
    ! [X3] :
      ( r2_hidden(X3,k5_xboole_0(sK0,sK1))
      | ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,sK1) ) ),
    inference(forward_demodulation,[],[f132,f173])).

fof(f132,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f85,f90])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1043,plain,(
    ~ r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f1013])).

fof(f1013,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK1) ),
    inference(backward_demodulation,[],[f220,f987])).

fof(f220,plain,
    ( ~ r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK1)
    | sK0 != sK1 ),
    inference(resolution,[],[f195,f50])).

fof(f195,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | sK0 != sK1 ),
    inference(backward_demodulation,[],[f88,f173])).

fof(f88,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 != sK1 ),
    inference(forward_demodulation,[],[f70,f72])).

fof(f70,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f30,f69])).

fof(f30,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f1061,plain,(
    r2_hidden(sK5(k5_xboole_0(sK0,sK0),sK0),sK0) ),
    inference(forward_demodulation,[],[f1040,f987])).

fof(f1040,plain,(
    r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f1032])).

fof(f1032,plain,
    ( sK0 != sK0
    | r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK0) ),
    inference(backward_demodulation,[],[f561,f987])).

fof(f561,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK0)
    | sK0 != sK1 ),
    inference(resolution,[],[f219,f251])).

fof(f251,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k5_xboole_0(sK0,sK1))
      | r2_hidden(X5,sK0) ) ),
    inference(forward_demodulation,[],[f134,f173])).

fof(f134,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k3_subset_1(sK0,sK1))
      | r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f87,f90])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f219,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK0,sK1))
    | sK0 != sK1 ),
    inference(resolution,[],[f195,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3223)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.20/0.47  % (3215)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.20/0.49  % (3239)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 0.20/0.50  % (3231)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.20/0.50  % (3214)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.20/0.51  % (3225)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (3216)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.20/0.51  % (3211)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.20/0.52  % (3225)Refutation not found, incomplete strategy% (3225)------------------------------
% 0.20/0.52  % (3225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3225)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3225)Memory used [KB]: 6140
% 0.20/0.52  % (3225)Time elapsed: 0.092 s
% 0.20/0.52  % (3225)------------------------------
% 0.20/0.52  % (3225)------------------------------
% 0.20/0.52  % (3234)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (3212)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (3228)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.20/0.52  % (3222)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 0.20/0.53  % (3219)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.20/0.53  % (3218)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.20/0.53  % (3214)Refutation not found, incomplete strategy% (3214)------------------------------
% 0.20/0.53  % (3214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3214)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3214)Memory used [KB]: 6140
% 0.20/0.53  % (3214)Time elapsed: 0.003 s
% 0.20/0.53  % (3214)------------------------------
% 0.20/0.53  % (3214)------------------------------
% 0.20/0.53  % (3213)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.20/0.53  % (3238)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.20/0.53  % (3230)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 0.20/0.53  % (3213)Refutation not found, incomplete strategy% (3213)------------------------------
% 0.20/0.53  % (3213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3213)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3213)Memory used [KB]: 6140
% 0.20/0.53  % (3213)Time elapsed: 0.126 s
% 0.20/0.53  % (3213)------------------------------
% 0.20/0.53  % (3213)------------------------------
% 0.20/0.53  % (3227)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (3240)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (3229)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (3221)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 0.20/0.53  % (3217)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.20/0.54  % (3235)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (3226)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (3233)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.20/0.54  % (3220)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (3224)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.20/0.55  % (3232)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 0.20/0.55  % (3237)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 0.20/0.55  % (3237)Refutation not found, incomplete strategy% (3237)------------------------------
% 0.20/0.55  % (3237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3237)Memory used [KB]: 10746
% 0.20/0.55  % (3237)Time elapsed: 0.150 s
% 0.20/0.55  % (3237)------------------------------
% 0.20/0.55  % (3237)------------------------------
% 0.20/0.55  % (3236)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (3235)Refutation not found, incomplete strategy% (3235)------------------------------
% 0.20/0.56  % (3235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (3235)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (3235)Memory used [KB]: 10618
% 0.20/0.56  % (3235)Time elapsed: 0.133 s
% 0.20/0.56  % (3235)------------------------------
% 0.20/0.56  % (3235)------------------------------
% 1.89/0.62  % (3262)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 1.89/0.62  % (3224)Refutation found. Thanks to Tanya!
% 1.89/0.62  % SZS status Theorem for theBenchmark
% 1.89/0.62  % SZS output start Proof for theBenchmark
% 1.89/0.62  fof(f1105,plain,(
% 1.89/0.62    $false),
% 1.89/0.62    inference(resolution,[],[f1061,f1055])).
% 1.89/0.62  fof(f1055,plain,(
% 1.89/0.62    ~r2_hidden(sK5(k5_xboole_0(sK0,sK0),sK0),sK0)),
% 1.89/0.62    inference(forward_demodulation,[],[f1043,f987])).
% 1.89/0.62  fof(f987,plain,(
% 1.89/0.62    sK0 = sK1),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f979])).
% 1.89/0.62  fof(f979,plain,(
% 1.89/0.62    sK0 = sK1 | sK0 = sK1),
% 1.89/0.62    inference(resolution,[],[f978,f222])).
% 1.89/0.62  fof(f222,plain,(
% 1.89/0.62    r2_hidden(sK5(sK0,sK1),sK0) | sK0 = sK1),
% 1.89/0.62    inference(resolution,[],[f174,f49])).
% 1.89/0.62  fof(f49,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f24])).
% 1.89/0.62  fof(f24,plain,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f2])).
% 1.89/0.62  fof(f2,axiom,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.89/0.62  fof(f174,plain,(
% 1.89/0.62    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 1.89/0.62    inference(superposition,[],[f144,f51])).
% 1.89/0.62  fof(f51,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.89/0.62    inference(cnf_transformation,[],[f25])).
% 1.89/0.62  fof(f25,plain,(
% 1.89/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.89/0.62    inference(ennf_transformation,[],[f8])).
% 1.89/0.62  fof(f8,axiom,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.89/0.62  fof(f144,plain,(
% 1.89/0.62    sK1 = k3_xboole_0(sK0,sK1)),
% 1.89/0.62    inference(superposition,[],[f119,f40])).
% 1.89/0.62  fof(f40,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f1])).
% 1.89/0.62  fof(f1,axiom,(
% 1.89/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.89/0.62  fof(f119,plain,(
% 1.89/0.62    sK1 = k3_xboole_0(sK1,sK0)),
% 1.89/0.62    inference(resolution,[],[f113,f51])).
% 1.89/0.62  fof(f113,plain,(
% 1.89/0.62    r1_tarski(sK1,sK0)),
% 1.89/0.62    inference(resolution,[],[f99,f59])).
% 1.89/0.62  fof(f59,plain,(
% 1.89/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f15])).
% 1.89/0.62  fof(f15,axiom,(
% 1.89/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.89/0.62  fof(f99,plain,(
% 1.89/0.62    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK0)),
% 1.89/0.62    inference(resolution,[],[f93,f83])).
% 1.89/0.62  fof(f83,plain,(
% 1.89/0.62    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(equality_resolution,[],[f45])).
% 1.89/0.62  fof(f45,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.89/0.62    inference(cnf_transformation,[],[f10])).
% 1.89/0.62  fof(f10,axiom,(
% 1.89/0.62    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.89/0.62  fof(f93,plain,(
% 1.89/0.62    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.89/0.62    inference(resolution,[],[f31,f57])).
% 1.89/0.62  fof(f57,plain,(
% 1.89/0.62    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f28])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f11])).
% 1.89/0.62  fof(f11,axiom,(
% 1.89/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.89/0.62  fof(f31,plain,(
% 1.89/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.89/0.62    inference(cnf_transformation,[],[f22])).
% 1.89/0.62  fof(f22,plain,(
% 1.89/0.62    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f20])).
% 1.89/0.62  fof(f20,negated_conjecture,(
% 1.89/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.89/0.62    inference(negated_conjecture,[],[f19])).
% 1.89/0.62  fof(f19,conjecture,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.89/0.62  fof(f978,plain,(
% 1.89/0.62    ~r2_hidden(sK5(sK0,sK1),sK0) | sK0 = sK1),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f972])).
% 1.89/0.62  fof(f972,plain,(
% 1.89/0.62    ~r2_hidden(sK5(sK0,sK1),sK0) | sK0 = sK1 | sK0 = sK1),
% 1.89/0.62    inference(resolution,[],[f955,f223])).
% 1.89/0.62  fof(f223,plain,(
% 1.89/0.62    ~r2_hidden(sK5(sK0,sK1),sK1) | sK0 = sK1),
% 1.89/0.62    inference(resolution,[],[f174,f50])).
% 1.89/0.62  fof(f50,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f24])).
% 1.89/0.62  fof(f955,plain,(
% 1.89/0.62    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | sK0 = sK1) )),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f935])).
% 1.89/0.62  fof(f935,plain,(
% 1.89/0.62    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1) | sK0 = sK1 | r2_hidden(X0,sK1)) )),
% 1.89/0.62    inference(resolution,[],[f744,f198])).
% 1.89/0.62  fof(f198,plain,(
% 1.89/0.62    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK0,sK1)) | sK0 = sK1 | r2_hidden(X0,sK1)) )),
% 1.89/0.62    inference(resolution,[],[f193,f48])).
% 1.89/0.62  fof(f48,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f24])).
% 1.89/0.62  fof(f193,plain,(
% 1.89/0.62    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 1.89/0.62    inference(backward_demodulation,[],[f89,f173])).
% 1.89/0.62  fof(f173,plain,(
% 1.89/0.62    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.89/0.62    inference(backward_demodulation,[],[f90,f144])).
% 1.89/0.62  fof(f90,plain,(
% 1.89/0.62    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.89/0.62    inference(resolution,[],[f31,f73])).
% 1.89/0.62  fof(f73,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f53,f66])).
% 1.89/0.62  fof(f66,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f7])).
% 1.89/0.62  fof(f7,axiom,(
% 1.89/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.89/0.62  fof(f53,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f27])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f14])).
% 1.89/0.62  fof(f14,axiom,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.89/0.62  fof(f89,plain,(
% 1.89/0.62    r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 1.89/0.62    inference(forward_demodulation,[],[f71,f72])).
% 1.89/0.62  fof(f72,plain,(
% 1.89/0.62    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.89/0.62    inference(definition_unfolding,[],[f43,f69])).
% 1.89/0.62  fof(f69,plain,(
% 1.89/0.62    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f42,f67])).
% 1.89/0.62  fof(f67,plain,(
% 1.89/0.62    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f12])).
% 1.89/0.62  fof(f12,axiom,(
% 1.89/0.62    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.89/0.62  fof(f42,plain,(
% 1.89/0.62    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f17])).
% 1.89/0.62  fof(f17,axiom,(
% 1.89/0.62    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.89/0.62  fof(f43,plain,(
% 1.89/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.89/0.62    inference(cnf_transformation,[],[f13])).
% 1.89/0.62  fof(f13,axiom,(
% 1.89/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.89/0.62  fof(f71,plain,(
% 1.89/0.62    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.89/0.62    inference(definition_unfolding,[],[f29,f69])).
% 1.89/0.62  fof(f29,plain,(
% 1.89/0.62    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.89/0.62    inference(cnf_transformation,[],[f22])).
% 1.89/0.62  fof(f744,plain,(
% 1.89/0.62    ( ! [X3] : (r2_hidden(X3,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X3,sK0) | r2_hidden(X3,sK1)) )),
% 1.89/0.62    inference(forward_demodulation,[],[f132,f173])).
% 1.89/0.62  fof(f132,plain,(
% 1.89/0.62    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,sK0) | r2_hidden(X3,sK1)) )),
% 1.89/0.62    inference(superposition,[],[f85,f90])).
% 1.89/0.62  fof(f85,plain,(
% 1.89/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.89/0.62    inference(equality_resolution,[],[f74])).
% 1.89/0.62  fof(f74,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.89/0.62    inference(definition_unfolding,[],[f65,f66])).
% 1.89/0.62  fof(f65,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.89/0.62    inference(cnf_transformation,[],[f4])).
% 1.89/0.62  fof(f4,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.89/0.62  fof(f1043,plain,(
% 1.89/0.62    ~r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK1)),
% 1.89/0.62    inference(trivial_inequality_removal,[],[f1013])).
% 1.89/0.62  fof(f1013,plain,(
% 1.89/0.62    sK0 != sK0 | ~r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK1)),
% 1.89/0.62    inference(backward_demodulation,[],[f220,f987])).
% 1.89/0.62  fof(f220,plain,(
% 1.89/0.62    ~r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK1) | sK0 != sK1),
% 1.89/0.62    inference(resolution,[],[f195,f50])).
% 1.89/0.62  fof(f195,plain,(
% 1.89/0.62    ~r1_tarski(k5_xboole_0(sK0,sK1),sK1) | sK0 != sK1),
% 1.89/0.62    inference(backward_demodulation,[],[f88,f173])).
% 1.89/0.62  fof(f88,plain,(
% 1.89/0.62    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 != sK1),
% 1.89/0.62    inference(forward_demodulation,[],[f70,f72])).
% 1.89/0.62  fof(f70,plain,(
% 1.89/0.62    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.89/0.62    inference(definition_unfolding,[],[f30,f69])).
% 1.89/0.62  fof(f30,plain,(
% 1.89/0.62    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.89/0.62    inference(cnf_transformation,[],[f22])).
% 1.89/0.62  fof(f1061,plain,(
% 1.89/0.62    r2_hidden(sK5(k5_xboole_0(sK0,sK0),sK0),sK0)),
% 1.89/0.62    inference(forward_demodulation,[],[f1040,f987])).
% 1.89/0.62  fof(f1040,plain,(
% 1.89/0.62    r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK0)),
% 1.89/0.62    inference(trivial_inequality_removal,[],[f1032])).
% 1.89/0.62  fof(f1032,plain,(
% 1.89/0.62    sK0 != sK0 | r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK0)),
% 1.89/0.62    inference(backward_demodulation,[],[f561,f987])).
% 1.89/0.62  fof(f561,plain,(
% 1.89/0.62    r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),sK0) | sK0 != sK1),
% 1.89/0.62    inference(resolution,[],[f219,f251])).
% 1.89/0.62  fof(f251,plain,(
% 1.89/0.62    ( ! [X5] : (~r2_hidden(X5,k5_xboole_0(sK0,sK1)) | r2_hidden(X5,sK0)) )),
% 1.89/0.62    inference(forward_demodulation,[],[f134,f173])).
% 1.89/0.62  fof(f134,plain,(
% 1.89/0.62    ( ! [X5] : (~r2_hidden(X5,k3_subset_1(sK0,sK1)) | r2_hidden(X5,sK0)) )),
% 1.89/0.62    inference(superposition,[],[f87,f90])).
% 1.89/0.62  fof(f87,plain,(
% 1.89/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.89/0.62    inference(equality_resolution,[],[f76])).
% 1.89/0.62  fof(f76,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.89/0.62    inference(definition_unfolding,[],[f63,f66])).
% 1.89/0.62  fof(f63,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.89/0.62    inference(cnf_transformation,[],[f4])).
% 1.89/0.62  fof(f219,plain,(
% 1.89/0.62    r2_hidden(sK5(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK0,sK1)) | sK0 != sK1),
% 1.89/0.62    inference(resolution,[],[f195,f49])).
% 1.89/0.62  % SZS output end Proof for theBenchmark
% 1.89/0.62  % (3224)------------------------------
% 1.89/0.62  % (3224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (3224)Termination reason: Refutation
% 1.89/0.62  
% 1.89/0.62  % (3224)Memory used [KB]: 2302
% 1.89/0.62  % (3224)Time elapsed: 0.205 s
% 1.89/0.62  % (3224)------------------------------
% 1.89/0.62  % (3224)------------------------------
% 1.89/0.63  % (3210)Success in time 0.271 s
%------------------------------------------------------------------------------
