%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:54 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 373 expanded)
%              Number of leaves         :   11 ( 112 expanded)
%              Depth                    :   20
%              Number of atoms          :  221 (1793 expanded)
%              Number of equality atoms :   78 ( 480 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(subsumption_resolution,[],[f429,f47])).

fof(f47,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f429,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f86,f428])).

fof(f428,plain,(
    sK0 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f427,f131])).

fof(f131,plain,(
    r2_hidden(sK2(sK1),sK0) ),
    inference(backward_demodulation,[],[f65,f127])).

fof(f127,plain,(
    sK3(sK0) = sK2(sK1) ),
    inference(subsumption_resolution,[],[f120,f46])).

fof(f46,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f120,plain,
    ( sK3(sK0) = sK2(sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f90,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0),X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f90,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | sK2(sK1) = X3 ) ),
    inference(superposition,[],[f63,f86])).

fof(f63,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f65,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f43,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f427,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | sK0 = k1_tarski(sK2(sK1)) ),
    inference(trivial_inequality_removal,[],[f424])).

fof(f424,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | sK0 = k1_tarski(sK2(sK1))
    | sK2(sK1) != sK2(sK1) ),
    inference(superposition,[],[f57,f421])).

fof(f421,plain,(
    sK2(sK1) = sK4(sK2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f415,f47])).

fof(f415,plain,
    ( sK2(sK1) = sK4(sK2(sK1),sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f411])).

fof(f411,plain,
    ( sK2(sK1) = sK4(sK2(sK1),sK0)
    | sK0 = sK1
    | sK2(sK1) = sK4(sK2(sK1),sK0) ),
    inference(resolution,[],[f87,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK2(sK1) = X0 ) ),
    inference(resolution,[],[f90,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f46,f48])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2(sK1),X0),X0)
      | sK2(sK1) = sK4(sK2(sK1),X0)
      | sK1 = X0 ) ),
    inference(superposition,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f75,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f72,f45])).

fof(f45,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f44,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f74,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f71,f45])).

fof(f71,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:53:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (25558)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.53  % (25551)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (25566)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.53  % (25546)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.53  % (25539)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (25543)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.53  % (25548)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.54  % (25542)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.54  % (25561)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.54  % (25565)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.54  % (25553)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.54  % (25567)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.54  % (25544)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (25540)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (25541)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (25540)Refutation not found, incomplete strategy% (25540)------------------------------
% 0.23/0.55  % (25540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (25540)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (25540)Memory used [KB]: 10746
% 0.23/0.55  % (25540)Time elapsed: 0.115 s
% 0.23/0.55  % (25540)------------------------------
% 0.23/0.55  % (25540)------------------------------
% 0.23/0.55  % (25538)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (25550)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (25559)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (25547)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (25557)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.56  % (25548)Refutation not found, incomplete strategy% (25548)------------------------------
% 0.23/0.56  % (25548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (25548)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (25548)Memory used [KB]: 10618
% 0.23/0.56  % (25548)Time elapsed: 0.137 s
% 0.23/0.56  % (25548)------------------------------
% 0.23/0.56  % (25548)------------------------------
% 0.23/0.56  % (25545)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.56  % (25552)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.56  % (25563)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  % (25560)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.57  % (25560)Refutation not found, incomplete strategy% (25560)------------------------------
% 1.47/0.57  % (25560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (25560)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (25560)Memory used [KB]: 10746
% 1.47/0.57  % (25560)Time elapsed: 0.151 s
% 1.47/0.57  % (25560)------------------------------
% 1.47/0.57  % (25560)------------------------------
% 1.47/0.57  % (25554)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.57  % (25555)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.58  % (25562)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.58  % (25538)Refutation found. Thanks to Tanya!
% 1.47/0.58  % SZS status Theorem for theBenchmark
% 1.47/0.58  % SZS output start Proof for theBenchmark
% 1.47/0.58  fof(f430,plain,(
% 1.47/0.58    $false),
% 1.47/0.58    inference(subsumption_resolution,[],[f429,f47])).
% 1.47/0.58  fof(f47,plain,(
% 1.47/0.58    sK0 != sK1),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f30,plain,(
% 1.47/0.58    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29,f28])).
% 1.47/0.58  fof(f28,plain,(
% 1.47/0.58    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f29,plain,(
% 1.47/0.58    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f22,plain,(
% 1.47/0.58    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.47/0.58    inference(flattening,[],[f21])).
% 1.47/0.58  fof(f21,plain,(
% 1.47/0.58    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.47/0.58    inference(ennf_transformation,[],[f19])).
% 1.47/0.58  fof(f19,negated_conjecture,(
% 1.47/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.47/0.58    inference(negated_conjecture,[],[f18])).
% 1.47/0.58  fof(f18,conjecture,(
% 1.47/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.47/0.58  fof(f429,plain,(
% 1.47/0.58    sK0 = sK1),
% 1.47/0.58    inference(backward_demodulation,[],[f86,f428])).
% 1.47/0.58  fof(f428,plain,(
% 1.47/0.58    sK0 = k1_tarski(sK2(sK1))),
% 1.47/0.58    inference(subsumption_resolution,[],[f427,f131])).
% 1.47/0.58  fof(f131,plain,(
% 1.47/0.58    r2_hidden(sK2(sK1),sK0)),
% 1.47/0.58    inference(backward_demodulation,[],[f65,f127])).
% 1.47/0.58  fof(f127,plain,(
% 1.47/0.58    sK3(sK0) = sK2(sK1)),
% 1.47/0.58    inference(subsumption_resolution,[],[f120,f46])).
% 1.47/0.58  fof(f46,plain,(
% 1.47/0.58    r1_tarski(sK0,sK1)),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f120,plain,(
% 1.47/0.58    sK3(sK0) = sK2(sK1) | ~r1_tarski(sK0,sK1)),
% 1.47/0.58    inference(resolution,[],[f90,f80])).
% 1.47/0.58  fof(f80,plain,(
% 1.47/0.58    ( ! [X0] : (r2_hidden(sK3(sK0),X0) | ~r1_tarski(sK0,X0)) )),
% 1.47/0.58    inference(resolution,[],[f65,f48])).
% 1.47/0.58  fof(f48,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f23])).
% 1.47/0.58  fof(f23,plain,(
% 1.47/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f20])).
% 1.47/0.58  fof(f20,plain,(
% 1.47/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.58    inference(unused_predicate_definition_removal,[],[f2])).
% 1.47/0.58  fof(f2,axiom,(
% 1.47/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.58  fof(f90,plain,(
% 1.47/0.58    ( ! [X3] : (~r2_hidden(X3,sK1) | sK2(sK1) = X3) )),
% 1.47/0.58    inference(superposition,[],[f63,f86])).
% 1.47/0.58  fof(f63,plain,(
% 1.47/0.58    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.47/0.58    inference(equality_resolution,[],[f54])).
% 1.47/0.58  fof(f54,plain,(
% 1.47/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.47/0.58    inference(cnf_transformation,[],[f42])).
% 1.47/0.58  fof(f42,plain,(
% 1.47/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.47/0.58  fof(f41,plain,(
% 1.47/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f40,plain,(
% 1.47/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.58    inference(rectify,[],[f39])).
% 1.47/0.58  fof(f39,plain,(
% 1.47/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.58    inference(nnf_transformation,[],[f10])).
% 1.47/0.58  fof(f10,axiom,(
% 1.47/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.47/0.58  fof(f65,plain,(
% 1.47/0.58    r2_hidden(sK3(sK0),sK0)),
% 1.47/0.58    inference(resolution,[],[f43,f53])).
% 1.47/0.58  fof(f53,plain,(
% 1.47/0.58    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f38])).
% 1.47/0.58  fof(f38,plain,(
% 1.47/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.47/0.58  fof(f37,plain,(
% 1.47/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f36,plain,(
% 1.47/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.58    inference(rectify,[],[f35])).
% 1.47/0.58  fof(f35,plain,(
% 1.47/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.58    inference(nnf_transformation,[],[f1])).
% 1.47/0.58  fof(f1,axiom,(
% 1.47/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.58  fof(f43,plain,(
% 1.47/0.58    ~v1_xboole_0(sK0)),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f427,plain,(
% 1.47/0.58    ~r2_hidden(sK2(sK1),sK0) | sK0 = k1_tarski(sK2(sK1))),
% 1.47/0.58    inference(trivial_inequality_removal,[],[f424])).
% 1.47/0.58  fof(f424,plain,(
% 1.47/0.58    ~r2_hidden(sK2(sK1),sK0) | sK0 = k1_tarski(sK2(sK1)) | sK2(sK1) != sK2(sK1)),
% 1.47/0.58    inference(superposition,[],[f57,f421])).
% 1.47/0.58  fof(f421,plain,(
% 1.47/0.58    sK2(sK1) = sK4(sK2(sK1),sK0)),
% 1.47/0.58    inference(subsumption_resolution,[],[f415,f47])).
% 1.47/0.58  fof(f415,plain,(
% 1.47/0.58    sK2(sK1) = sK4(sK2(sK1),sK0) | sK0 = sK1),
% 1.47/0.58    inference(duplicate_literal_removal,[],[f411])).
% 1.47/0.58  fof(f411,plain,(
% 1.47/0.58    sK2(sK1) = sK4(sK2(sK1),sK0) | sK0 = sK1 | sK2(sK1) = sK4(sK2(sK1),sK0)),
% 1.47/0.58    inference(resolution,[],[f87,f115])).
% 1.47/0.58  fof(f115,plain,(
% 1.47/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | sK2(sK1) = X0) )),
% 1.47/0.58    inference(resolution,[],[f90,f78])).
% 1.47/0.58  fof(f78,plain,(
% 1.47/0.58    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.47/0.58    inference(resolution,[],[f46,f48])).
% 1.47/0.58  fof(f87,plain,(
% 1.47/0.58    ( ! [X0] : (r2_hidden(sK4(sK2(sK1),X0),X0) | sK2(sK1) = sK4(sK2(sK1),X0) | sK1 = X0) )),
% 1.47/0.58    inference(superposition,[],[f86,f56])).
% 1.47/0.58  fof(f56,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f42])).
% 1.47/0.58  fof(f57,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f42])).
% 1.47/0.58  fof(f86,plain,(
% 1.47/0.58    sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.58    inference(forward_demodulation,[],[f85,f75])).
% 1.47/0.58  fof(f75,plain,(
% 1.47/0.58    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 1.47/0.58    inference(subsumption_resolution,[],[f72,f45])).
% 1.47/0.58  fof(f45,plain,(
% 1.47/0.58    v1_zfmisc_1(sK1)),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f72,plain,(
% 1.47/0.58    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1)),
% 1.47/0.58    inference(resolution,[],[f44,f50])).
% 1.47/0.58  fof(f50,plain,(
% 1.47/0.58    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f34])).
% 1.47/0.58  fof(f34,plain,(
% 1.47/0.58    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.47/0.58  fof(f33,plain,(
% 1.47/0.58    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f32,plain,(
% 1.47/0.58    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.47/0.58    inference(rectify,[],[f31])).
% 1.47/0.58  fof(f31,plain,(
% 1.47/0.58    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.47/0.58    inference(nnf_transformation,[],[f24])).
% 1.47/0.58  fof(f24,plain,(
% 1.47/0.58    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.47/0.58    inference(ennf_transformation,[],[f17])).
% 1.47/0.58  fof(f17,axiom,(
% 1.47/0.58    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.47/0.58  fof(f44,plain,(
% 1.47/0.58    ~v1_xboole_0(sK1)),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f85,plain,(
% 1.47/0.58    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 1.47/0.58    inference(subsumption_resolution,[],[f83,f44])).
% 1.47/0.58  fof(f83,plain,(
% 1.47/0.58    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1)),
% 1.47/0.58    inference(resolution,[],[f74,f58])).
% 1.47/0.58  fof(f58,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f26])).
% 1.47/0.58  fof(f26,plain,(
% 1.47/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.47/0.58    inference(flattening,[],[f25])).
% 1.47/0.58  fof(f25,plain,(
% 1.47/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f16])).
% 1.47/0.58  fof(f16,axiom,(
% 1.47/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.47/0.58  fof(f74,plain,(
% 1.47/0.58    m1_subset_1(sK2(sK1),sK1)),
% 1.47/0.58    inference(subsumption_resolution,[],[f71,f45])).
% 1.47/0.58  fof(f71,plain,(
% 1.47/0.58    m1_subset_1(sK2(sK1),sK1) | ~v1_zfmisc_1(sK1)),
% 1.47/0.58    inference(resolution,[],[f44,f49])).
% 1.47/0.58  fof(f49,plain,(
% 1.47/0.58    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f34])).
% 1.47/0.58  % SZS output end Proof for theBenchmark
% 1.47/0.58  % (25538)------------------------------
% 1.47/0.58  % (25538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (25538)Termination reason: Refutation
% 1.47/0.58  
% 1.47/0.58  % (25538)Memory used [KB]: 1918
% 1.47/0.58  % (25538)Time elapsed: 0.158 s
% 1.47/0.58  % (25538)------------------------------
% 1.47/0.58  % (25538)------------------------------
% 1.47/0.58  % (25537)Success in time 0.207 s
%------------------------------------------------------------------------------
