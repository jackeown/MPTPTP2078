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
% DateTime   : Thu Dec  3 12:45:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  73 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 327 expanded)
%              Number of equality atoms :   14 (  49 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23,f24,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f100,f58])).

% (29536)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(sK4(X2,X3,X0),X2) ) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
        & r2_hidden(sK5(X1,X2,X3),X2)
        & r2_hidden(sK4(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f21])).

fof(f21,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
        & r2_hidden(sK5(X1,X2,X3),X2)
        & r2_hidden(sK4(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(sK4(sK0,sK1,sK3),sK0) ) ),
    inference(subsumption_resolution,[],[f95,f23])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK2)
      | ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(sK4(sK0,sK1,sK3),sK0) ) ),
    inference(resolution,[],[f90,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X1,X2,sK3),sK1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(sK4(X1,X2,sK3),sK0) ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X4,X5] :
      ( ~ sQ6_eqProxy(k4_tarski(X4,X5),sK3)
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(equality_proxy_replacement,[],[f25,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f25,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK3
            | ~ m1_subset_1(X5,sK1) )
        | ~ m1_subset_1(X4,sK0) )
    & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    & r2_hidden(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK3
              | ~ m1_subset_1(X5,sK1) )
          | ~ m1_subset_1(X4,sK0) )
      & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ6_eqProxy(k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)),X3)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f37,f38])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,X0),sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f60,f24])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(sK5(X2,X3,X0),X3) ) ),
    inference(resolution,[],[f36,f55])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (29523)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (29527)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (29526)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (29523)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (29531)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f23,f24,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK3,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f58])).
% 0.22/0.51  % (29536)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(X0,X1) | m1_subset_1(sK4(X2,X3,X0),X2)) )),
% 0.22/0.51    inference(resolution,[],[f35,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f27,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 & r2_hidden(sK5(X1,X2,X3),X2) & r2_hidden(sK4(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 & r2_hidden(sK5(X1,X2,X3),X2) & r2_hidden(sK4(X1,X2,X3),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK3,X0) | ~m1_subset_1(sK4(sK0,sK1,sK3),sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f95,f23])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK3,sK2) | ~r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK3,X0) | ~m1_subset_1(sK4(sK0,sK1,sK3),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f90,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X1,X2,sK3),sK1) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK3,X0) | ~m1_subset_1(sK4(X1,X2,sK3),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f41,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~sQ6_eqProxy(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 0.22/0.51    inference(equality_proxy_replacement,[],[f25,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2)) => (! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (sQ6_eqProxy(k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)),X3) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.51    inference(equality_proxy_replacement,[],[f37,f38])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,X0),sK1) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f60,f24])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(X0,X1) | m1_subset_1(sK5(X2,X3,X0),X3)) )),
% 0.22/0.51    inference(resolution,[],[f36,f55])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    r2_hidden(sK3,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (29523)------------------------------
% 0.22/0.51  % (29523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29523)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (29523)Memory used [KB]: 6140
% 0.22/0.51  % (29523)Time elapsed: 0.070 s
% 0.22/0.51  % (29523)------------------------------
% 0.22/0.51  % (29523)------------------------------
% 0.22/0.51  % (29517)Success in time 0.143 s
%------------------------------------------------------------------------------
