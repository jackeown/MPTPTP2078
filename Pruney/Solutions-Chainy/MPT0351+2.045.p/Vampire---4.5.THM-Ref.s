%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:09 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 180 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 623 expanded)
%              Number of equality atoms :   56 ( 185 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f658,plain,(
    $false ),
    inference(subsumption_resolution,[],[f657,f79])).

fof(f79,plain,(
    sK0 != k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[],[f49,f72])).

fof(f72,plain,(
    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f66,f59])).

fof(f59,plain,(
    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f25,f24])).

fof(f24,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f66,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f64,f38])).

% (2266)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f37,f37])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f57,f22])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k4_subset_1(X1,X2,X1) ) ),
    inference(resolution,[],[f39,f50])).

fof(f49,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f23,f24])).

fof(f23,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f657,plain,(
    sK0 = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f59,f639])).

fof(f639,plain,(
    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,
    ( sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f633,f306])).

fof(f306,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,X2),X3)
      | k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = X2 ) ),
    inference(subsumption_resolution,[],[f296,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f296,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,X2),X2)
      | r2_hidden(sK2(X2,X3,X2),X3)
      | k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = X2 ) ),
    inference(factoring,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f633,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(sK0,X2,sK0),sK1)
      | sK0 = k5_xboole_0(sK0,k5_xboole_0(X2,k3_xboole_0(X2,sK0))) ) ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(sK0,X2,sK0),sK1)
      | sK0 = k5_xboole_0(sK0,k5_xboole_0(X2,k3_xboole_0(X2,sK0)))
      | sK0 = k5_xboole_0(sK0,k5_xboole_0(X2,k3_xboole_0(X2,sK0))) ) ),
    inference(resolution,[],[f618,f306])).

fof(f618,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,sK0),X1)
      | ~ r2_hidden(sK2(X0,X1,sK0),sK1)
      | sK0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ) ),
    inference(resolution,[],[f82,f22])).

fof(f82,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X8,X7))) = X9
      | ~ r2_hidden(sK2(X7,X8,X9),X10)
      | ~ r2_hidden(sK2(X7,X8,X9),X8) ) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ) ),
    inference(definition_unfolding,[],[f36,f37])).

% (2266)Refutation not found, incomplete strategy% (2266)------------------------------
% (2266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2266)Termination reason: Refutation not found, incomplete strategy

% (2266)Memory used [KB]: 1663
% (2266)Time elapsed: 0.105 s
% (2266)------------------------------
% (2266)------------------------------
fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:08:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.44  % (2269)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.45  % (2287)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.46  % (2295)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.47  % (2287)Refutation not found, incomplete strategy% (2287)------------------------------
% 0.18/0.47  % (2287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (2287)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (2287)Memory used [KB]: 10618
% 0.18/0.48  % (2287)Time elapsed: 0.087 s
% 0.18/0.48  % (2287)------------------------------
% 0.18/0.48  % (2287)------------------------------
% 0.18/0.50  % (2267)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.50  % (2268)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.50  % (2271)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.51  % (2290)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.51  % (2272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.51  % (2269)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f658,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(subsumption_resolution,[],[f657,f79])).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    sK0 != k4_subset_1(sK0,sK0,sK1)),
% 0.18/0.51    inference(superposition,[],[f49,f72])).
% 0.18/0.51  fof(f72,plain,(
% 0.18/0.51    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 0.18/0.51    inference(forward_demodulation,[],[f66,f59])).
% 0.18/0.51  fof(f59,plain,(
% 0.18/0.51    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 0.18/0.51    inference(resolution,[],[f56,f50])).
% 0.18/0.51  fof(f50,plain,(
% 0.18/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(forward_demodulation,[],[f25,f24])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.18/0.51    inference(cnf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.18/0.51  fof(f25,plain,(
% 0.18/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f6])).
% 0.18/0.51  fof(f6,axiom,(
% 0.18/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.18/0.51  fof(f56,plain,(
% 0.18/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) )),
% 0.18/0.51    inference(resolution,[],[f39,f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(cnf_transformation,[],[f16])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.18/0.51  fof(f15,plain,(
% 0.18/0.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f11,plain,(
% 0.18/0.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,negated_conjecture,(
% 0.18/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.18/0.51    inference(negated_conjecture,[],[f9])).
% 0.18/0.51  fof(f9,conjecture,(
% 0.18/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.18/0.51  fof(f39,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f30,f37])).
% 0.18/0.51  fof(f37,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f28,f27])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f4])).
% 0.18/0.51  fof(f4,axiom,(
% 0.18/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f14])).
% 0.18/0.51  fof(f14,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(flattening,[],[f13])).
% 0.18/0.51  fof(f13,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.18/0.51    inference(ennf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.18/0.51  fof(f66,plain,(
% 0.18/0.51    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 0.18/0.51    inference(superposition,[],[f64,f38])).
% 0.18/0.51  % (2266)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.51  fof(f38,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f26,f37,f37])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.18/0.51  fof(f64,plain,(
% 0.18/0.51    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),
% 0.18/0.51    inference(resolution,[],[f57,f22])).
% 0.18/0.51  fof(f57,plain,(
% 0.18/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k4_subset_1(X1,X2,X1)) )),
% 0.18/0.51    inference(resolution,[],[f39,f50])).
% 0.18/0.51  fof(f49,plain,(
% 0.18/0.51    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.18/0.51    inference(backward_demodulation,[],[f23,f24])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.18/0.51    inference(cnf_transformation,[],[f16])).
% 0.18/0.51  fof(f657,plain,(
% 0.18/0.51    sK0 = k4_subset_1(sK0,sK0,sK1)),
% 0.18/0.51    inference(forward_demodulation,[],[f59,f639])).
% 0.18/0.51  fof(f639,plain,(
% 0.18/0.51    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f635])).
% 0.18/0.51  fof(f635,plain,(
% 0.18/0.51    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 0.18/0.51    inference(resolution,[],[f633,f306])).
% 0.18/0.51  fof(f306,plain,(
% 0.18/0.51    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,X2),X3) | k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = X2) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f296,f41])).
% 0.18/0.51  fof(f41,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2) )),
% 0.18/0.51    inference(definition_unfolding,[],[f35,f37])).
% 0.18/0.51  fof(f35,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f21])).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(rectify,[],[f18])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(flattening,[],[f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(nnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.18/0.51  fof(f296,plain,(
% 0.18/0.51    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,X2),X2) | r2_hidden(sK2(X2,X3,X2),X3) | k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = X2) )),
% 0.18/0.51    inference(factoring,[],[f42])).
% 0.18/0.51  fof(f42,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2) )),
% 0.18/0.51    inference(definition_unfolding,[],[f34,f37])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f21])).
% 0.18/0.51  fof(f633,plain,(
% 0.18/0.51    ( ! [X2] : (~r2_hidden(sK2(sK0,X2,sK0),sK1) | sK0 = k5_xboole_0(sK0,k5_xboole_0(X2,k3_xboole_0(X2,sK0)))) )),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f624])).
% 0.18/0.51  fof(f624,plain,(
% 0.18/0.51    ( ! [X2] : (~r2_hidden(sK2(sK0,X2,sK0),sK1) | sK0 = k5_xboole_0(sK0,k5_xboole_0(X2,k3_xboole_0(X2,sK0))) | sK0 = k5_xboole_0(sK0,k5_xboole_0(X2,k3_xboole_0(X2,sK0)))) )),
% 0.18/0.51    inference(resolution,[],[f618,f306])).
% 0.18/0.51  fof(f618,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1,sK0),X1) | ~r2_hidden(sK2(X0,X1,sK0),sK1) | sK0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.18/0.51    inference(resolution,[],[f82,f22])).
% 0.18/0.51  fof(f82,plain,(
% 0.18/0.51    ( ! [X10,X8,X7,X9] : (~m1_subset_1(X10,k1_zfmisc_1(X9)) | k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X8,X7))) = X9 | ~r2_hidden(sK2(X7,X8,X9),X10) | ~r2_hidden(sK2(X7,X8,X9),X8)) )),
% 0.18/0.51    inference(resolution,[],[f40,f29])).
% 0.18/0.51  fof(f29,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f12])).
% 0.18/0.51  fof(f12,plain,(
% 0.18/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,axiom,(
% 0.18/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2) )),
% 0.18/0.51    inference(definition_unfolding,[],[f36,f37])).
% 0.18/0.51  % (2266)Refutation not found, incomplete strategy% (2266)------------------------------
% 0.18/0.51  % (2266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (2266)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (2266)Memory used [KB]: 1663
% 0.18/0.51  % (2266)Time elapsed: 0.105 s
% 0.18/0.51  % (2266)------------------------------
% 0.18/0.51  % (2266)------------------------------
% 0.18/0.51  fof(f36,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f21])).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (2269)------------------------------
% 0.18/0.51  % (2269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (2269)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (2269)Memory used [KB]: 11129
% 0.18/0.51  % (2269)Time elapsed: 0.122 s
% 0.18/0.51  % (2269)------------------------------
% 0.18/0.51  % (2269)------------------------------
% 0.18/0.51  % (2273)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.51  % (2265)Success in time 0.163 s
%------------------------------------------------------------------------------
