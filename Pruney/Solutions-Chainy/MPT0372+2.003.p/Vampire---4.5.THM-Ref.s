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
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 323 expanded)
%              Number of leaves         :    9 (  79 expanded)
%              Depth                    :   26
%              Number of atoms          :  177 (1063 expanded)
%              Number of equality atoms :   34 ( 186 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(resolution,[],[f378,f352])).

fof(f352,plain,(
    r2_hidden(sK6(sK0,sK2,sK1),sK0) ),
    inference(resolution,[],[f347,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f59,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f56,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f21,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f55,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f18,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).

fof(f347,plain,(
    r2_hidden(sK6(sK0,sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f346,f18])).

fof(f346,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f341,f19])).

fof(f19,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f341,plain,
    ( sK1 = k3_subset_1(sK0,sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f340,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f340,plain,
    ( sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f339,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,sK1),sK0)
      | r2_hidden(sK6(X0,X1,sK1),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK1 ) ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f64,f30])).

fof(f64,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f57,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f28])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f339,plain,
    ( sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,
    ( sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f333,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f333,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK1)
    | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK1)
    | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,sK2,sK1),sK1)
    | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f219,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f219,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK0,X0,sK1),sK2)
      | r2_hidden(sK6(sK0,X0,sK1),sK1)
      | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ) ),
    inference(resolution,[],[f217,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f78,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f16,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f217,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK0,X0,sK1),sK0)
      | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ) ),
    inference(factoring,[],[f72])).

fof(f378,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(subsumption_resolution,[],[f377,f18])).

fof(f377,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f370,f19])).

fof(f370,plain,(
    ! [X0] :
      ( sK1 = k3_subset_1(sK0,sK2)
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f366,f43])).

fof(f366,plain,(
    ! [X2] :
      ( sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f362,f23])).

fof(f362,plain,
    ( v1_xboole_0(sK0)
    | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f351,f333])).

fof(f351,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f347,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f68])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f17,f27])).

fof(f17,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:12:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (1484)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.47  % (1492)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.50  % (1472)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (1473)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (1477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.51  % (1487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (1470)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (1475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (1469)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (1480)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (1490)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (1471)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (1485)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  % (1482)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (1483)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (1495)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (1494)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (1497)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (1490)Refutation not found, incomplete strategy% (1490)------------------------------
% 0.19/0.53  % (1490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (1490)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (1490)Memory used [KB]: 10746
% 0.19/0.53  % (1490)Time elapsed: 0.098 s
% 0.19/0.53  % (1490)------------------------------
% 0.19/0.53  % (1490)------------------------------
% 0.19/0.53  % (1493)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.53  % (1474)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.53  % (1491)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.54  % (1478)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.54  % (1496)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (1478)Refutation not found, incomplete strategy% (1478)------------------------------
% 1.37/0.54  % (1478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (1478)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (1478)Memory used [KB]: 10618
% 1.37/0.54  % (1478)Time elapsed: 0.141 s
% 1.37/0.54  % (1478)------------------------------
% 1.37/0.54  % (1478)------------------------------
% 1.37/0.54  % (1476)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.54  % (1486)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.54  % (1468)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (1489)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.54  % (1479)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (1481)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.55  % (1488)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.57  % (1489)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f391,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(resolution,[],[f378,f352])).
% 1.54/0.57  fof(f352,plain,(
% 1.54/0.57    r2_hidden(sK6(sK0,sK2,sK1),sK0)),
% 1.54/0.57    inference(resolution,[],[f347,f63])).
% 1.54/0.57  fof(f63,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 1.54/0.57    inference(resolution,[],[f59,f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f15])).
% 1.54/0.57  fof(f15,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.57  fof(f59,plain,(
% 1.54/0.57    r1_tarski(sK2,sK0)),
% 1.54/0.57    inference(resolution,[],[f56,f50])).
% 1.54/0.57  fof(f50,plain,(
% 1.54/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.54/0.57    inference(equality_resolution,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f5])).
% 1.54/0.57  fof(f5,axiom,(
% 1.54/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(subsumption_resolution,[],[f55,f21])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(resolution,[],[f18,f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f13])).
% 1.54/0.57  fof(f13,plain,(
% 1.54/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.54/0.57  fof(f18,plain,(
% 1.54/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(cnf_transformation,[],[f12])).
% 1.54/0.57  fof(f12,plain,(
% 1.54/0.57    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.57    inference(flattening,[],[f11])).
% 1.54/0.57  fof(f11,plain,(
% 1.54/0.57    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 1.54/0.57    inference(negated_conjecture,[],[f9])).
% 1.54/0.57  fof(f9,conjecture,(
% 1.54/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).
% 1.54/0.57  fof(f347,plain,(
% 1.54/0.57    r2_hidden(sK6(sK0,sK2,sK1),sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f346,f18])).
% 1.54/0.57  fof(f346,plain,(
% 1.54/0.57    r2_hidden(sK6(sK0,sK2,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(subsumption_resolution,[],[f341,f19])).
% 1.54/0.57  fof(f19,plain,(
% 1.54/0.57    sK1 != k3_subset_1(sK0,sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f12])).
% 1.54/0.57  fof(f341,plain,(
% 1.54/0.57    sK1 = k3_subset_1(sK0,sK2) | r2_hidden(sK6(sK0,sK2,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(superposition,[],[f340,f43])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.57    inference(definition_unfolding,[],[f29,f24])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f4])).
% 1.54/0.57  fof(f4,axiom,(
% 1.54/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,plain,(
% 1.54/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.54/0.57  fof(f340,plain,(
% 1.54/0.57    sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,sK2,sK1),sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f339,f72])).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,sK1),sK0) | r2_hidden(sK6(X0,X1,sK1),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK1) )),
% 1.54/0.57    inference(resolution,[],[f68,f48])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.54/0.57    inference(definition_unfolding,[],[f38,f24])).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.54/0.57    inference(resolution,[],[f64,f30])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    r1_tarski(sK1,sK0)),
% 1.54/0.57    inference(resolution,[],[f58,f50])).
% 1.54/0.57  fof(f58,plain,(
% 1.54/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(subsumption_resolution,[],[f57,f21])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(resolution,[],[f20,f28])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.57    inference(cnf_transformation,[],[f12])).
% 1.54/0.57  fof(f339,plain,(
% 1.54/0.57    sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,sK2,sK1),sK2) | ~r2_hidden(sK6(sK0,sK2,sK1),sK0)),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f338])).
% 1.54/0.57  fof(f338,plain,(
% 1.54/0.57    sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,sK2,sK1),sK2) | ~r2_hidden(sK6(sK0,sK2,sK1),sK0) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.54/0.57    inference(resolution,[],[f333,f49])).
% 1.54/0.57  fof(f49,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.54/0.57    inference(definition_unfolding,[],[f37,f24])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f3])).
% 1.54/0.57  fof(f333,plain,(
% 1.54/0.57    r2_hidden(sK6(sK0,sK2,sK1),sK1) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f330])).
% 1.54/0.57  fof(f330,plain,(
% 1.54/0.57    r2_hidden(sK6(sK0,sK2,sK1),sK1) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,sK2,sK1),sK1) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.54/0.57    inference(resolution,[],[f219,f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.54/0.57    inference(definition_unfolding,[],[f39,f24])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f3])).
% 1.54/0.57  fof(f219,plain,(
% 1.54/0.57    ( ! [X0] : (r2_hidden(sK6(sK0,X0,sK1),sK2) | r2_hidden(sK6(sK0,X0,sK1),sK1) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 1.54/0.57    inference(resolution,[],[f217,f79])).
% 1.54/0.57  fof(f79,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f78,f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.54/0.57  fof(f78,plain,(
% 1.54/0.57    ( ! [X0] : (r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.54/0.57    inference(resolution,[],[f16,f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f13])).
% 1.54/0.57  fof(f16,plain,(
% 1.54/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f12])).
% 1.54/0.57  fof(f217,plain,(
% 1.54/0.57    ( ! [X0] : (r2_hidden(sK6(sK0,X0,sK1),sK0) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 1.54/0.57    inference(factoring,[],[f72])).
% 1.54/0.57  fof(f378,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f377,f18])).
% 1.54/0.57  fof(f377,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f370,f19])).
% 1.54/0.57  fof(f370,plain,(
% 1.54/0.57    ( ! [X0] : (sK1 = k3_subset_1(sK0,sK2) | ~r2_hidden(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))) )),
% 1.54/0.57    inference(superposition,[],[f366,f43])).
% 1.54/0.57  fof(f366,plain,(
% 1.54/0.57    ( ! [X2] : (sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~r2_hidden(X2,sK0)) )),
% 1.54/0.57    inference(resolution,[],[f362,f23])).
% 1.54/0.57  fof(f362,plain,(
% 1.54/0.57    v1_xboole_0(sK0) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.54/0.57    inference(resolution,[],[f351,f333])).
% 1.54/0.57  fof(f351,plain,(
% 1.54/0.57    ~r2_hidden(sK6(sK0,sK2,sK1),sK1) | v1_xboole_0(sK0)),
% 1.54/0.57    inference(resolution,[],[f347,f82])).
% 1.54/0.57  fof(f82,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | v1_xboole_0(sK0)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f81,f68])).
% 1.54/0.57  fof(f81,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.54/0.57    inference(resolution,[],[f17,f27])).
% 1.54/0.57  fof(f17,plain,(
% 1.54/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f12])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (1489)------------------------------
% 1.54/0.57  % (1489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (1489)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (1489)Memory used [KB]: 1918
% 1.54/0.57  % (1489)Time elapsed: 0.175 s
% 1.54/0.57  % (1489)------------------------------
% 1.54/0.57  % (1489)------------------------------
% 1.54/0.57  % (1467)Success in time 0.219 s
%------------------------------------------------------------------------------
