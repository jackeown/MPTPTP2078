%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  71 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 321 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f35,plain,(
    r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f25,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

% (444)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
fof(f12,plain,
    ( ~ r1_tarski(sK1,sK2)
    & ! [X3] :
        ( r2_hidden(X3,sK2)
        | ~ m1_subset_1(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & ! [X3] :
                ( r2_hidden(X3,X2)
                | ~ m1_subset_1(X3,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ m1_subset_1(X3,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,X2)
        & ! [X3] :
            ( r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,sK2)
      & ! [X3] :
          ( r2_hidden(X3,sK2)
          | ~ m1_subset_1(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ m1_subset_1(X3,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ m1_subset_1(X3,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => r2_hidden(X3,X2) )
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => r2_hidden(X3,X2) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

fof(f81,plain,(
    ~ r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    ~ r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f48,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f24,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (436)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.47  % (436)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f81,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r2_hidden(sK4(sK1,sK2),sK1)),
% 0.20/0.47    inference(resolution,[],[f25,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ~r1_tarski(sK1,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % (444)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~m1_subset_1(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11,f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~m1_subset_1(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~m1_subset_1(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~m1_subset_1(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~m1_subset_1(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X1) => r2_hidden(X3,X2)) => r1_tarski(X1,X2))))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X1) => r2_hidden(X3,X2)) => r1_tarski(X1,X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK1,sK2),sK1)),
% 0.20/0.47    inference(resolution,[],[f50,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK1,sK2),sK2)),
% 0.20/0.47    inference(resolution,[],[f25,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f48,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(resolution,[],[f35,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(rectify,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | v1_xboole_0(sK1)) )),
% 0.20/0.47    inference(resolution,[],[f24,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X3] : (~m1_subset_1(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (436)------------------------------
% 0.20/0.47  % (436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (436)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (436)Memory used [KB]: 5373
% 0.20/0.47  % (436)Time elapsed: 0.053 s
% 0.20/0.47  % (436)------------------------------
% 0.20/0.47  % (436)------------------------------
% 0.20/0.47  % (424)Success in time 0.117 s
%------------------------------------------------------------------------------
