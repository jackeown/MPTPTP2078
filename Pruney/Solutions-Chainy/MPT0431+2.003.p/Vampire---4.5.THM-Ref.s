%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 113 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 443 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f34,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f33,f15])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f33,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f14,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f104,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f97,f36])).

fof(f36,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f35,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f17,f21])).

fof(f17,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f93,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f93,plain,(
    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f62,f82])).

fof(f82,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f81,f15])).

fof(f81,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f80,f18])).

% (27970)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f80,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f22,f59])).

fof(f59,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f45,f18])).

fof(f45,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | k2_xboole_0(X0,sK2) = k4_subset_1(k1_zfmisc_1(sK0),X0,sK2) ) ),
    inference(resolution,[],[f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f62,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f60,f59])).

fof(f60,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f55,f59])).

fof(f55,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f16,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:28:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (27962)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (27969)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (27969)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (27961)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f104,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f33,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK0,sK2)),
% 0.22/0.48    inference(resolution,[],[f14,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    v3_setfam_1(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    r2_hidden(sK0,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f97,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f35,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f17,f21])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    v3_setfam_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK2)),
% 0.22/0.48    inference(resolution,[],[f93,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    r2_hidden(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.48    inference(resolution,[],[f62,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f15])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f18])).
% 0.22/0.48  % (27970)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(superposition,[],[f22,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(resolution,[],[f45,f18])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k2_xboole_0(X0,sK2) = k4_subset_1(k1_zfmisc_1(sK0),X0,sK2)) )),
% 0.22/0.48    inference(resolution,[],[f15,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f60,f59])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(backward_demodulation,[],[f55,f59])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ~m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))),
% 0.22/0.48    inference(resolution,[],[f16,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27969)------------------------------
% 0.22/0.48  % (27969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27969)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27969)Memory used [KB]: 1663
% 0.22/0.48  % (27969)Time elapsed: 0.064 s
% 0.22/0.48  % (27969)------------------------------
% 0.22/0.48  % (27969)------------------------------
% 0.22/0.48  % (27955)Success in time 0.12 s
%------------------------------------------------------------------------------
