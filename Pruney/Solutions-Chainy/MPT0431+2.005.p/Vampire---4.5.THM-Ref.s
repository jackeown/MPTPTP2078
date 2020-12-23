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
% DateTime   : Thu Dec  3 12:46:50 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 152 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 524 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11901)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f227,f206])).

fof(f206,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(k4_xboole_0(X0,sK1),sK2)) ),
    inference(forward_demodulation,[],[f203,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f203,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,k3_tarski(k1_enumset1(sK1,sK1,sK2)))) ),
    inference(backward_demodulation,[],[f109,f189])).

fof(f189,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k3_tarski(k1_enumset1(sK1,sK1,sK2)) ),
    inference(resolution,[],[f51,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | k4_subset_1(k1_zfmisc_1(sK0),sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)) ) ),
    inference(resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f109,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))) ),
    inference(resolution,[],[f106,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f106,plain,(
    r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f102,f19])).

fof(f19,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,
    ( r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))
    | v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(resolution,[],[f96,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f96,plain,(
    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f52,f18])).

fof(f52,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(resolution,[],[f21,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f227,plain,(
    r2_hidden(sK0,k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(sK1,sK1,sK2)),sK1),sK2)) ),
    inference(resolution,[],[f201,f48])).

fof(f48,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,X1)
      | r2_hidden(sK0,k4_xboole_0(X1,sK2)) ) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f43,f17])).

fof(f17,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ v3_setfam_1(sK2,sK0) ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f201,plain,(
    r2_hidden(sK0,k4_xboole_0(k3_tarski(k1_enumset1(sK1,sK1,sK2)),sK1)) ),
    inference(backward_demodulation,[],[f107,f189])).

fof(f107,plain,(
    r2_hidden(sK0,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK1)) ),
    inference(resolution,[],[f106,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,X1)
      | r2_hidden(sK0,k4_xboole_0(X1,sK1)) ) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f50,f20])).

fof(f20,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_setfam_1(sK1,sK0) ),
    inference(resolution,[],[f21,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (11898)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (11897)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (11920)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (11903)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (11902)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (11908)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (11909)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11918)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (11910)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.53  % (11912)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.53  % (11899)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (11904)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.53  % (11914)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.53  % (11905)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.53  % (11911)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.53  % (11916)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.53  % (11921)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.53  % (11913)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.54  % (11923)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.54  % (11925)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (11906)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (11900)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (11918)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  % (11901)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  fof(f229,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(subsumption_resolution,[],[f227,f206])).
% 1.37/0.54  fof(f206,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(k4_xboole_0(X0,sK1),sK2))) )),
% 1.37/0.54    inference(forward_demodulation,[],[f203,f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f27,f36])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f23,f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.37/0.54  fof(f203,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,k3_tarski(k1_enumset1(sK1,sK1,sK2))))) )),
% 1.37/0.54    inference(backward_demodulation,[],[f109,f189])).
% 1.37/0.54  fof(f189,plain,(
% 1.37/0.54    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k3_tarski(k1_enumset1(sK1,sK1,sK2))),
% 1.37/0.54    inference(resolution,[],[f51,f18])).
% 1.37/0.54  fof(f18,plain,(
% 1.37/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.37/0.54    inference(flattening,[],[f10])).
% 1.37/0.54  fof(f10,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))) & ~v1_xboole_0(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f9])).
% 1.37/0.54  fof(f9,negated_conjecture,(
% 1.37/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 1.37/0.54    inference(negated_conjecture,[],[f8])).
% 1.37/0.54  fof(f8,conjecture,(
% 1.37/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_setfam_1)).
% 1.37/0.54  fof(f51,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k4_subset_1(k1_zfmisc_1(sK0),sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0))) )),
% 1.37/0.54    inference(resolution,[],[f21,f38])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f29,f36])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.54    inference(flattening,[],[f15])).
% 1.37/0.54  fof(f15,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f109,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)))) )),
% 1.37/0.54    inference(resolution,[],[f106,f40])).
% 1.37/0.54  fof(f40,plain,(
% 1.37/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(equality_resolution,[],[f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.37/0.54  fof(f106,plain,(
% 1.37/0.54    r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))),
% 1.37/0.54    inference(subsumption_resolution,[],[f102,f19])).
% 1.37/0.54  fof(f19,plain,(
% 1.37/0.54    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f102,plain,(
% 1.37/0.54    r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) | v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 1.37/0.54    inference(resolution,[],[f96,f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f12])).
% 1.37/0.54  fof(f12,plain,(
% 1.37/0.54    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).
% 1.37/0.54  fof(f96,plain,(
% 1.37/0.54    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.37/0.54    inference(resolution,[],[f52,f18])).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X1),k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 1.37/0.54    inference(resolution,[],[f21,f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.54    inference(flattening,[],[f13])).
% 1.37/0.54  fof(f13,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.37/0.54  fof(f227,plain,(
% 1.37/0.54    r2_hidden(sK0,k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(sK1,sK1,sK2)),sK1),sK2))),
% 1.37/0.54    inference(resolution,[],[f201,f48])).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK0,k4_xboole_0(X1,sK2))) )),
% 1.37/0.54    inference(resolution,[],[f46,f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(equality_resolution,[],[f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ~r2_hidden(sK0,sK2)),
% 1.37/0.54    inference(subsumption_resolution,[],[f43,f17])).
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    v3_setfam_1(sK2,sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    ~r2_hidden(sK0,sK2) | ~v3_setfam_1(sK2,sK0)),
% 1.37/0.54    inference(resolution,[],[f18,f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f12])).
% 1.37/0.54  fof(f201,plain,(
% 1.37/0.54    r2_hidden(sK0,k4_xboole_0(k3_tarski(k1_enumset1(sK1,sK1,sK2)),sK1))),
% 1.37/0.54    inference(backward_demodulation,[],[f107,f189])).
% 1.37/0.54  fof(f107,plain,(
% 1.37/0.54    r2_hidden(sK0,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK1))),
% 1.37/0.54    inference(resolution,[],[f106,f55])).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK0,k4_xboole_0(X1,sK1))) )),
% 1.37/0.54    inference(resolution,[],[f53,f39])).
% 1.37/0.54  fof(f53,plain,(
% 1.37/0.54    ~r2_hidden(sK0,sK1)),
% 1.37/0.54    inference(subsumption_resolution,[],[f50,f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    v3_setfam_1(sK1,sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f50,plain,(
% 1.37/0.54    ~r2_hidden(sK0,sK1) | ~v3_setfam_1(sK1,sK0)),
% 1.37/0.54    inference(resolution,[],[f21,f26])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (11918)------------------------------
% 1.37/0.54  % (11918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (11918)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (11918)Memory used [KB]: 1791
% 1.37/0.54  % (11918)Time elapsed: 0.138 s
% 1.37/0.54  % (11918)------------------------------
% 1.37/0.54  % (11918)------------------------------
% 1.37/0.55  % (11896)Success in time 0.179 s
%------------------------------------------------------------------------------
