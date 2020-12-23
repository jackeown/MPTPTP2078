%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 159 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  208 ( 833 expanded)
%              Number of equality atoms :  106 ( 396 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f112])).

fof(f112,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f108,f108])).

fof(f108,plain,(
    ! [X2] : k1_funct_1(sK1(sK0),sK3(k1_xboole_0,sK0)) = X2 ),
    inference(subsumption_resolution,[],[f103,f25])).

fof(f103,plain,(
    ! [X2] :
      ( k1_funct_1(sK1(sK0),sK3(k1_xboole_0,sK0)) = X2
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f57,f101])).

% (11804)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f101,plain,(
    ! [X0] : sK1(sK0) = sK2(sK0,X0) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X2
      | sK0 != X0
      | sK2(X0,X1) = sK1(X2) ) ),
    inference(superposition,[],[f95,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f20])).

% (11806)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f95,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK2(X2,X3))
      | sK0 != X4
      | sK2(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f93,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK2(X2,X3))
      | sK0 != X4
      | ~ v1_relat_1(sK2(X2,X3))
      | sK2(X2,X3) = sK1(X4) ) ),
    inference(resolution,[],[f89,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK0 != k1_relat_1(X0)
      | sK0 != X1
      | ~ v1_relat_1(X0)
      | sK1(X1) = X0 ) ),
    inference(forward_demodulation,[],[f88,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(X0)
      | sK0 != k1_relat_1(sK1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK1(X1) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(X0)
      | sK0 != k1_relat_1(sK1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK1(X1) = X0
      | ~ v1_relat_1(sK1(X1)) ) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

% (11805)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2(X0,X1),sK3(k1_xboole_0,X0)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK2(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (11802)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11820)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (11813)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (11813)Refutation not found, incomplete strategy% (11813)------------------------------
% 0.21/0.51  % (11813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11803)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11813)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11813)Memory used [KB]: 6140
% 0.21/0.51  % (11813)Time elapsed: 0.056 s
% 0.21/0.51  % (11813)------------------------------
% 0.21/0.51  % (11813)------------------------------
% 0.21/0.51  % (11800)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11819)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (11819)Refutation not found, incomplete strategy% (11819)------------------------------
% 0.21/0.51  % (11819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11812)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (11803)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f25,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.52    inference(superposition,[],[f108,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2] : (k1_funct_1(sK1(sK0),sK3(k1_xboole_0,sK0)) = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f25])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2] : (k1_funct_1(sK1(sK0),sK3(k1_xboole_0,sK0)) = X2 | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(superposition,[],[f57,f101])).
% 0.21/0.52  % (11804)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (sK1(sK0) = sK2(sK0,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK0 != X0 | sK2(X0,X1) = sK1(sK0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sK0 != X2 | sK0 != X0 | sK2(X0,X1) = sK1(X2)) )),
% 0.21/0.52    inference(superposition,[],[f95,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % (11806)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK2(X2,X3)) | sK0 != X4 | sK2(X2,X3) = sK1(X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f93,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK2(X2,X3)) | sK0 != X4 | ~v1_relat_1(sK2(X2,X3)) | sK2(X2,X3) = sK1(X4)) )),
% 0.21/0.52    inference(resolution,[],[f89,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | sK0 != k1_relat_1(X0) | sK0 != X1 | ~v1_relat_1(X0) | sK1(X1) = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f88,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK0 != k1_relat_1(X0) | sK0 != k1_relat_1(sK1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK1(X1) = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f86,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK0 != k1_relat_1(X0) | sK0 != k1_relat_1(sK1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK1(X1) = X0 | ~v1_relat_1(sK1(X1))) )),
% 0.21/0.52    inference(resolution,[],[f24,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  % (11805)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_funct_1(sK2(X0,X1),sK3(k1_xboole_0,X0)) = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f49,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK2(X0,X1),X3) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f37,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f39,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11803)------------------------------
% 0.21/0.52  % (11803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11803)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11803)Memory used [KB]: 6268
% 0.21/0.52  % (11803)Time elapsed: 0.074 s
% 0.21/0.52  % (11803)------------------------------
% 0.21/0.52  % (11803)------------------------------
% 0.21/0.52  % (11795)Success in time 0.161 s
%------------------------------------------------------------------------------
