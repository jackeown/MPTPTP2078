%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:06 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   57 (  81 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 347 expanded)
%              Number of equality atoms :   60 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f108,f37])).

fof(f37,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f108,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,sK0) ),
    inference(superposition,[],[f38,f102])).

fof(f102,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f101,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

% (17802)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f99,f35])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
      | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f98,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X2] : r1_tarski(sK4(k1_zfmisc_1(X2)),X2) ),
    inference(subsumption_resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

% (17797)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f67,plain,(
    ! [X2] :
      ( r1_tarski(sK4(k1_zfmisc_1(X2)),X2)
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f76,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k1_tarski(X7))
      | k1_xboole_0 != k1_tarski(X7) ) ),
    inference(superposition,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(X1,k1_tarski(X0)) ),
    inference(superposition,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
      | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f56,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f38,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.24/0.52  % (17798)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.24/0.53  % (17789)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.24/0.53  % (17806)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.24/0.53  % (17783)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.24/0.53  % (17803)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.24/0.53  % (17782)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.54  % (17795)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.24/0.54  % (17781)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.54  % (17787)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.54  % (17798)Refutation not found, incomplete strategy% (17798)------------------------------
% 1.24/0.54  % (17798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (17789)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f109,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(subsumption_resolution,[],[f108,f37])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    r2_hidden(sK2,sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.24/0.54    inference(flattening,[],[f16])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.24/0.54    inference(ennf_transformation,[],[f14])).
% 1.24/0.54  fof(f14,negated_conjecture,(
% 1.24/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.24/0.54    inference(negated_conjecture,[],[f13])).
% 1.24/0.54  fof(f13,conjecture,(
% 1.24/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.24/0.54  fof(f108,plain,(
% 1.24/0.54    ~r2_hidden(sK2,sK0)),
% 1.24/0.54    inference(trivial_inequality_removal,[],[f105])).
% 1.24/0.54  fof(f105,plain,(
% 1.24/0.54    sK1 != sK1 | ~r2_hidden(sK2,sK0)),
% 1.24/0.54    inference(superposition,[],[f38,f102])).
% 1.24/0.54  fof(f102,plain,(
% 1.24/0.54    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) )),
% 1.24/0.54    inference(resolution,[],[f101,f61])).
% 1.24/0.54  fof(f61,plain,(
% 1.24/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.24/0.54    inference(equality_resolution,[],[f50])).
% 1.24/0.54  fof(f50,plain,(
% 1.24/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f33,plain,(
% 1.24/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 1.24/0.54  % (17802)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.54  fof(f32,plain,(
% 1.24/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f31,plain,(
% 1.24/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.54    inference(rectify,[],[f30])).
% 1.24/0.54  fof(f30,plain,(
% 1.24/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.54    inference(nnf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.24/0.54  fof(f101,plain,(
% 1.24/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~r2_hidden(X0,sK0)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f100,f34])).
% 1.24/0.54  fof(f34,plain,(
% 1.24/0.54    v1_funct_1(sK3)),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f100,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~v1_funct_1(sK3)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f99,f35])).
% 1.24/0.54  fof(f35,plain,(
% 1.24/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f99,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f98,f87])).
% 1.24/0.54  fof(f87,plain,(
% 1.24/0.54    ( ! [X0] : (k1_tarski(X0) != k1_xboole_0) )),
% 1.24/0.54    inference(resolution,[],[f76,f68])).
% 1.24/0.54  fof(f68,plain,(
% 1.24/0.54    ( ! [X2] : (r1_tarski(sK4(k1_zfmisc_1(X2)),X2)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f67,f39])).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f11])).
% 1.24/0.54  % (17797)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.24/0.54  fof(f11,axiom,(
% 1.24/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.24/0.54  fof(f67,plain,(
% 1.24/0.54    ( ! [X2] : (r1_tarski(sK4(k1_zfmisc_1(X2)),X2) | v1_xboole_0(k1_zfmisc_1(X2))) )),
% 1.24/0.54    inference(resolution,[],[f58,f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 1.24/0.54  fof(f24,plain,(
% 1.24/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f15])).
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.24/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 1.24/0.54  fof(f2,axiom,(
% 1.24/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.24/0.54  fof(f58,plain,(
% 1.24/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.24/0.54    inference(equality_resolution,[],[f46])).
% 1.24/0.54  fof(f46,plain,(
% 1.24/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.24/0.54    inference(cnf_transformation,[],[f29])).
% 1.24/0.54  fof(f29,plain,(
% 1.24/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.54    inference(rectify,[],[f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.54    inference(nnf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.24/0.54  fof(f76,plain,(
% 1.24/0.54    ( ! [X6,X7] : (~r1_tarski(X6,k1_tarski(X7)) | k1_xboole_0 != k1_tarski(X7)) )),
% 1.24/0.54    inference(superposition,[],[f62,f45])).
% 1.24/0.54  fof(f45,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.24/0.54  fof(f62,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(X1,k1_tarski(X0))) )),
% 1.24/0.54    inference(superposition,[],[f42,f43])).
% 1.24/0.54  fof(f43,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f10])).
% 1.24/0.54  fof(f10,axiom,(
% 1.24/0.54    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.24/0.54  fof(f98,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3)) )),
% 1.24/0.54    inference(resolution,[],[f56,f36])).
% 1.24/0.54  fof(f36,plain,(
% 1.24/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f56,plain,(
% 1.24/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f21])).
% 1.24/0.54  fof(f21,plain,(
% 1.24/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.24/0.54    inference(flattening,[],[f20])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.24/0.54    inference(ennf_transformation,[],[f12])).
% 1.24/0.54  fof(f12,axiom,(
% 1.24/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    sK1 != k1_funct_1(sK3,sK2)),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (17789)------------------------------
% 1.24/0.54  % (17789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (17789)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (17789)Memory used [KB]: 1791
% 1.24/0.54  % (17789)Time elapsed: 0.127 s
% 1.24/0.54  % (17789)------------------------------
% 1.24/0.54  % (17789)------------------------------
% 1.24/0.54  % (17780)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.54  % (17781)Refutation not found, incomplete strategy% (17781)------------------------------
% 1.24/0.54  % (17781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (17781)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (17781)Memory used [KB]: 1791
% 1.24/0.54  % (17781)Time elapsed: 0.095 s
% 1.24/0.54  % (17781)------------------------------
% 1.24/0.54  % (17781)------------------------------
% 1.24/0.54  % (17798)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (17798)Memory used [KB]: 1791
% 1.24/0.54  % (17798)Time elapsed: 0.117 s
% 1.24/0.54  % (17798)------------------------------
% 1.24/0.54  % (17798)------------------------------
% 1.24/0.54  % (17784)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.55  % (17779)Success in time 0.179 s
%------------------------------------------------------------------------------
