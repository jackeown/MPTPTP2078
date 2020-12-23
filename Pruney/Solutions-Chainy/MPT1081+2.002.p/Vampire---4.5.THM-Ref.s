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
% DateTime   : Thu Dec  3 13:08:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  77 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   16
%              Number of atoms          :  189 ( 359 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f86,plain,(
    v1_xboole_0(k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ m1_funct_2(k1_tarski(sK2),sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ m1_funct_2(k1_tarski(sK2),sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_funct_2)).

fof(f85,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f84,f23])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f83,f25])).

fof(f25,plain,(
    ~ m1_funct_2(k1_tarski(sK2),sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,
    ( m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f82,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k1_tarski(sK2)) ),
    inference(superposition,[],[f39,f78])).

fof(f78,plain,(
    sK2 = sK4(sK0,sK1,k1_tarski(sK2)) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f68,plain,(
    r2_hidden(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f65,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2))
    | v1_xboole_0(k1_tarski(sK2)) ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f46,plain,(
    m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f45,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2))
    | v1_xboole_0(k1_tarski(sK2)) ),
    inference(resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1)
      | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
      | ~ v1_funct_1(sK4(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (23848)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (23852)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (23849)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (23850)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (23861)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (23848)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f86,f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f85,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ~m1_funct_2(k1_tarski(sK2),sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~m1_funct_2(k1_tarski(sK2),sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f8,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f7])).
% 0.20/0.55  fof(f7,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => m1_funct_2(k1_tarski(X2),X0,X1))),
% 0.20/0.55    inference(negated_conjecture,[],[f5])).
% 0.20/0.55  fof(f5,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => m1_funct_2(k1_tarski(X2),X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_funct_2)).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f84,f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f83,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ~m1_funct_2(k1_tarski(sK2),sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    m1_funct_2(k1_tarski(sK2),sK0,sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f82,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_funct_2(k1_tarski(sK2),sK0,sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(superposition,[],[f39,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    sK2 = sK4(sK0,sK1,k1_tarski(sK2))),
% 0.20/0.55    inference(resolution,[],[f68,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    r2_hidden(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f65,f26])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    r2_hidden(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2)) | v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(resolution,[],[f46,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f45,f26])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_tarski(sK2)) | v1_xboole_0(k1_tarski(sK2))),
% 0.20/0.55    inference(resolution,[],[f25,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_funct_2(X2,X0,X1) | m1_subset_1(sK4(X0,X1,X2),X2) | v1_xboole_0(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ((~m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4(X0,X1,X2),X0,X1) | ~v1_funct_1(sK4(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2)) => ((~m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4(X0,X1,X2),X0,X1) | ~v1_funct_1(sK4(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),X2)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.20/0.55    inference(rectify,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.20/0.55    inference(nnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_funct_2(X2,X0,X1) <=> ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2))) | v1_xboole_0(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => (m1_funct_2(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,X2) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_funct_2(X2,X0,X1) | ~v1_funct_2(sK4(X0,X1,X2),X0,X1) | ~v1_funct_1(sK4(X0,X1,X2)) | v1_xboole_0(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (23848)------------------------------
% 0.20/0.55  % (23848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23848)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (23848)Memory used [KB]: 10618
% 0.20/0.55  % (23848)Time elapsed: 0.123 s
% 0.20/0.55  % (23848)------------------------------
% 0.20/0.55  % (23848)------------------------------
% 0.20/0.55  % (23846)Success in time 0.192 s
%------------------------------------------------------------------------------
