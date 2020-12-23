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
% DateTime   : Thu Dec  3 12:44:56 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 201 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f65,f73])).

fof(f73,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f69,f35])).

fof(f35,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f29,f34])).

fof(f34,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

% (6866)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f18,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f69,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f50,f21])).

fof(f21,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_3
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f65,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_4 ),
    inference(superposition,[],[f22,f54])).

fof(f54,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f46,f52,f49])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_xboole_0(X0,sK2)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X2
      | ~ r1_xboole_0(X4,X3)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f31,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:50:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.38  ipcrm: permission denied for id (730038273)
% 0.15/0.39  ipcrm: permission denied for id (730136580)
% 0.15/0.39  ipcrm: permission denied for id (730202118)
% 0.15/0.39  ipcrm: permission denied for id (730267655)
% 0.15/0.40  ipcrm: permission denied for id (730333193)
% 0.15/0.40  ipcrm: permission denied for id (730431500)
% 0.22/0.41  ipcrm: permission denied for id (730595345)
% 0.22/0.42  ipcrm: permission denied for id (730890264)
% 0.22/0.42  ipcrm: permission denied for id (730988571)
% 0.22/0.43  ipcrm: permission denied for id (731054110)
% 0.22/0.43  ipcrm: permission denied for id (731152417)
% 0.22/0.44  ipcrm: permission denied for id (731316262)
% 0.22/0.44  ipcrm: permission denied for id (731414569)
% 0.22/0.44  ipcrm: permission denied for id (731447338)
% 0.22/0.45  ipcrm: permission denied for id (731611183)
% 0.22/0.45  ipcrm: permission denied for id (731742259)
% 0.22/0.45  ipcrm: permission denied for id (731775028)
% 0.22/0.45  ipcrm: permission denied for id (731807797)
% 0.22/0.45  ipcrm: permission denied for id (731873335)
% 0.22/0.46  ipcrm: permission denied for id (732069950)
% 0.22/0.46  ipcrm: permission denied for id (732102719)
% 0.22/0.47  ipcrm: permission denied for id (732168257)
% 0.22/0.47  ipcrm: permission denied for id (732233795)
% 0.22/0.47  ipcrm: permission denied for id (732266564)
% 0.22/0.47  ipcrm: permission denied for id (732299333)
% 0.22/0.47  ipcrm: permission denied for id (732332102)
% 0.22/0.47  ipcrm: permission denied for id (732364871)
% 0.22/0.49  ipcrm: permission denied for id (732790868)
% 0.22/0.49  ipcrm: permission denied for id (732856406)
% 0.22/0.49  ipcrm: permission denied for id (732889175)
% 0.22/0.50  ipcrm: permission denied for id (732954713)
% 0.22/0.50  ipcrm: permission denied for id (733020251)
% 0.22/0.50  ipcrm: permission denied for id (733053020)
% 0.22/0.50  ipcrm: permission denied for id (733085789)
% 0.22/0.50  ipcrm: permission denied for id (733118558)
% 0.22/0.51  ipcrm: permission denied for id (733216864)
% 0.22/0.51  ipcrm: permission denied for id (733249633)
% 0.22/0.51  ipcrm: permission denied for id (733282402)
% 0.22/0.51  ipcrm: permission denied for id (733413477)
% 0.22/0.51  ipcrm: permission denied for id (733446246)
% 0.22/0.52  ipcrm: permission denied for id (733511783)
% 0.22/0.52  ipcrm: permission denied for id (733610091)
% 0.22/0.52  ipcrm: permission denied for id (733675629)
% 0.22/0.52  ipcrm: permission denied for id (733708398)
% 0.22/0.53  ipcrm: permission denied for id (733741167)
% 0.22/0.53  ipcrm: permission denied for id (733806705)
% 0.22/0.53  ipcrm: permission denied for id (733905012)
% 0.22/0.53  ipcrm: permission denied for id (733937781)
% 0.22/0.53  ipcrm: permission denied for id (733970550)
% 0.22/0.54  ipcrm: permission denied for id (734036088)
% 0.22/0.54  ipcrm: permission denied for id (734068857)
% 0.22/0.54  ipcrm: permission denied for id (734101626)
% 0.22/0.54  ipcrm: permission denied for id (734167164)
% 0.22/0.54  ipcrm: permission denied for id (734199933)
% 0.22/0.55  ipcrm: permission denied for id (734232702)
% 0.22/0.55  ipcrm: permission denied for id (734265471)
% 0.88/0.68  % (6875)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.88/0.69  % (6875)Refutation found. Thanks to Tanya!
% 0.88/0.69  % SZS status Theorem for theBenchmark
% 0.88/0.69  % (6882)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.88/0.69  % SZS output start Proof for theBenchmark
% 0.88/0.69  fof(f74,plain,(
% 0.88/0.69    $false),
% 0.88/0.69    inference(avatar_sat_refutation,[],[f55,f65,f73])).
% 0.88/0.69  fof(f73,plain,(
% 0.88/0.69    ~spl3_3),
% 0.88/0.69    inference(avatar_contradiction_clause,[],[f71])).
% 0.88/0.69  fof(f71,plain,(
% 0.88/0.69    $false | ~spl3_3),
% 0.88/0.69    inference(resolution,[],[f69,f35])).
% 0.88/0.69  fof(f35,plain,(
% 0.88/0.69    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.88/0.69    inference(superposition,[],[f29,f34])).
% 0.88/0.69  fof(f34,plain,(
% 0.88/0.69    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.88/0.69    inference(resolution,[],[f30,f19])).
% 0.88/0.69  fof(f19,plain,(
% 0.88/0.69    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.88/0.69    inference(cnf_transformation,[],[f18])).
% 0.88/0.69  % (6866)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.88/0.69  fof(f18,plain,(
% 0.88/0.69    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.88/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.88/0.69  fof(f17,plain,(
% 0.88/0.69    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.88/0.69    introduced(choice_axiom,[])).
% 0.88/0.69  fof(f10,plain,(
% 0.88/0.69    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.88/0.69    inference(flattening,[],[f9])).
% 0.88/0.69  fof(f9,plain,(
% 0.88/0.69    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.88/0.69    inference(ennf_transformation,[],[f8])).
% 0.88/0.69  fof(f8,negated_conjecture,(
% 0.88/0.69    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.88/0.69    inference(negated_conjecture,[],[f7])).
% 0.88/0.69  fof(f7,conjecture,(
% 0.88/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.88/0.69  fof(f30,plain,(
% 0.88/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.88/0.69    inference(definition_unfolding,[],[f27,f25])).
% 0.88/0.69  fof(f25,plain,(
% 0.88/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.88/0.69    inference(cnf_transformation,[],[f2])).
% 0.88/0.69  fof(f2,axiom,(
% 0.88/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.88/0.69  fof(f27,plain,(
% 0.88/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.88/0.69    inference(cnf_transformation,[],[f14])).
% 0.88/0.69  fof(f14,plain,(
% 0.88/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.88/0.69    inference(ennf_transformation,[],[f6])).
% 0.88/0.69  fof(f6,axiom,(
% 0.88/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.88/0.69  fof(f29,plain,(
% 0.88/0.69    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.88/0.69    inference(definition_unfolding,[],[f24,f25])).
% 0.88/0.69  fof(f24,plain,(
% 0.88/0.69    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.88/0.69    inference(cnf_transformation,[],[f5])).
% 0.88/0.69  fof(f5,axiom,(
% 0.88/0.69    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.88/0.69  fof(f69,plain,(
% 0.88/0.69    ~r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~spl3_3),
% 0.88/0.69    inference(resolution,[],[f50,f21])).
% 0.88/0.69  fof(f21,plain,(
% 0.88/0.69    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.88/0.69    inference(cnf_transformation,[],[f18])).
% 0.88/0.69  fof(f50,plain,(
% 0.88/0.69    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_xboole_0(X0,sK2)) ) | ~spl3_3),
% 0.88/0.69    inference(avatar_component_clause,[],[f49])).
% 0.88/0.69  fof(f49,plain,(
% 0.88/0.69    spl3_3 <=> ! [X0] : (~r1_xboole_0(X0,sK2) | ~r1_tarski(sK1,X0))),
% 0.88/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.88/0.69  fof(f65,plain,(
% 0.88/0.69    ~spl3_4),
% 0.88/0.69    inference(avatar_contradiction_clause,[],[f64])).
% 0.88/0.69  fof(f64,plain,(
% 0.88/0.69    $false | ~spl3_4),
% 0.88/0.69    inference(trivial_inequality_removal,[],[f63])).
% 0.88/0.69  fof(f63,plain,(
% 0.88/0.69    k1_xboole_0 != k1_xboole_0 | ~spl3_4),
% 0.88/0.69    inference(superposition,[],[f22,f54])).
% 0.88/0.69  fof(f54,plain,(
% 0.88/0.69    k1_xboole_0 = sK1 | ~spl3_4),
% 0.88/0.69    inference(avatar_component_clause,[],[f52])).
% 0.88/0.69  fof(f52,plain,(
% 0.88/0.69    spl3_4 <=> k1_xboole_0 = sK1),
% 0.88/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.88/0.69  fof(f22,plain,(
% 0.88/0.69    k1_xboole_0 != sK1),
% 0.88/0.69    inference(cnf_transformation,[],[f18])).
% 0.88/0.69  fof(f55,plain,(
% 0.88/0.69    spl3_3 | spl3_4),
% 0.88/0.69    inference(avatar_split_clause,[],[f46,f52,f49])).
% 0.88/0.69  fof(f46,plain,(
% 0.88/0.69    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_xboole_0(X0,sK2) | ~r1_tarski(sK1,X0)) )),
% 0.88/0.69    inference(resolution,[],[f33,f20])).
% 0.88/0.69  fof(f20,plain,(
% 0.88/0.69    r1_tarski(sK1,sK2)),
% 0.88/0.69    inference(cnf_transformation,[],[f18])).
% 0.88/0.69  fof(f33,plain,(
% 0.88/0.69    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | k1_xboole_0 = X2 | ~r1_xboole_0(X4,X3) | ~r1_tarski(X2,X4)) )),
% 0.88/0.69    inference(resolution,[],[f31,f28])).
% 0.88/0.69  fof(f28,plain,(
% 0.88/0.69    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.88/0.69    inference(cnf_transformation,[],[f16])).
% 0.88/0.69  fof(f16,plain,(
% 0.88/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.88/0.69    inference(flattening,[],[f15])).
% 0.88/0.69  fof(f15,plain,(
% 0.88/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.88/0.69    inference(ennf_transformation,[],[f3])).
% 0.88/0.69  fof(f3,axiom,(
% 0.88/0.69    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.88/0.69  fof(f31,plain,(
% 0.88/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 0.88/0.69    inference(resolution,[],[f26,f23])).
% 0.88/0.69  fof(f23,plain,(
% 0.88/0.69    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.88/0.69    inference(cnf_transformation,[],[f11])).
% 0.88/0.69  fof(f11,plain,(
% 0.88/0.69    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.88/0.69    inference(ennf_transformation,[],[f1])).
% 0.88/0.69  fof(f1,axiom,(
% 0.88/0.69    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.88/0.69  fof(f26,plain,(
% 0.88/0.69    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.88/0.69    inference(cnf_transformation,[],[f13])).
% 0.88/0.69  fof(f13,plain,(
% 0.88/0.69    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.88/0.69    inference(flattening,[],[f12])).
% 0.88/0.69  fof(f12,plain,(
% 0.88/0.69    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.88/0.69    inference(ennf_transformation,[],[f4])).
% 0.88/0.69  fof(f4,axiom,(
% 0.88/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.88/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.88/0.69  % SZS output end Proof for theBenchmark
% 0.88/0.69  % (6875)------------------------------
% 0.88/0.69  % (6875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.88/0.69  % (6875)Termination reason: Refutation
% 0.88/0.69  
% 0.88/0.69  % (6875)Memory used [KB]: 6140
% 0.88/0.69  % (6875)Time elapsed: 0.089 s
% 0.88/0.69  % (6875)------------------------------
% 0.88/0.69  % (6875)------------------------------
% 0.88/0.70  % (6696)Success in time 0.319 s
%------------------------------------------------------------------------------
