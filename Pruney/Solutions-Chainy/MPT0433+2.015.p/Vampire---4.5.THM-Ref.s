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
% DateTime   : Thu Dec  3 12:46:53 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 165 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  180 ( 429 expanded)
%              Number of equality atoms :   19 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1712,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f853,f1199,f1711])).

fof(f1711,plain,(
    spl2_22 ),
    inference(avatar_contradiction_clause,[],[f1710])).

fof(f1710,plain,
    ( $false
    | spl2_22 ),
    inference(subsumption_resolution,[],[f1705,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1705,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl2_22 ),
    inference(resolution,[],[f1703,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1703,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | spl2_22 ),
    inference(superposition,[],[f1697,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1697,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK1)
    | spl2_22 ),
    inference(resolution,[],[f1695,f47])).

fof(f1695,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(k2_xboole_0(X0,X1),sK1) )
    | spl2_22 ),
    inference(superposition,[],[f1678,f41])).

fof(f1678,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(sK1,X0),X1),sK1)
    | spl2_22 ),
    inference(resolution,[],[f1221,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f1221,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X5),X3)
        | ~ r1_tarski(k2_xboole_0(X3,X4),sK1) )
    | spl2_22 ),
    inference(resolution,[],[f1208,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1208,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ r1_tarski(k2_xboole_0(X0,X1),sK1) )
    | spl2_22 ),
    inference(resolution,[],[f1205,f42])).

fof(f1205,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),X0) )
    | spl2_22 ),
    inference(superposition,[],[f1203,f41])).

fof(f1203,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),sK1)
    | spl2_22 ),
    inference(resolution,[],[f1202,f42])).

fof(f1202,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_22 ),
    inference(subsumption_resolution,[],[f1201,f47])).

fof(f1201,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_22 ),
    inference(superposition,[],[f1197,f41])).

fof(f1197,plain,
    ( ~ r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f1195])).

fof(f1195,plain,
    ( spl2_22
  <=> r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f1199,plain,
    ( ~ spl2_22
    | spl2_2 ),
    inference(avatar_split_clause,[],[f1178,f71,f1195])).

fof(f71,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1178,plain,
    ( ~ r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1))
    | spl2_2 ),
    inference(superposition,[],[f866,f453])).

fof(f453,plain,(
    ! [X2] : k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X2),sK1)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X2)),k1_relat_1(sK1)) ),
    inference(resolution,[],[f109,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f109,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK0)
      | k1_relat_1(k2_xboole_0(X5,sK1)) = k2_xboole_0(k1_relat_1(X5),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f51,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f866,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK1))
    | spl2_2 ),
    inference(resolution,[],[f73,f42])).

fof(f73,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f853,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f852])).

fof(f852,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f851,f36])).

fof(f851,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f850,f47])).

fof(f850,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_1 ),
    inference(superposition,[],[f843,f41])).

fof(f843,plain,
    ( ~ r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),k1_relat_1(sK0))
    | spl2_1 ),
    inference(superposition,[],[f75,f350])).

fof(f350,plain,(
    ! [X2] : k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X2),sK0)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X2)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f95,f36])).

fof(f95,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK0)
      | k1_relat_1(k2_xboole_0(X5,sK0)) = k2_xboole_0(k1_relat_1(X5),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f49,f52])).

fof(f49,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X1,sK0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f30,f33])).

fof(f75,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK0))
    | spl2_1 ),
    inference(resolution,[],[f69,f42])).

fof(f69,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f74,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f64,f71,f67])).

fof(f64,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f32,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (2571)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (2578)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (2565)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (2580)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (2576)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (2582)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (2564)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (2584)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (2563)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (2583)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.38/0.53  % (2559)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.38/0.53  % (2560)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.53  % (2568)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.54  % (2575)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.38/0.54  % (2577)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.38/0.54  % (2585)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.38/0.54  % (2574)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.38/0.54  % (2572)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.38/0.55  % (2569)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.38/0.55  % (2567)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.55  % (2570)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.51/0.55  % (2562)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.51/0.55  % (2561)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.51/0.56  % (2573)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.51/0.57  % (2579)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.51/0.57  % (2566)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.51/0.59  % (2565)Refutation found. Thanks to Tanya!
% 1.51/0.59  % SZS status Theorem for theBenchmark
% 1.51/0.61  % SZS output start Proof for theBenchmark
% 1.51/0.61  fof(f1712,plain,(
% 1.51/0.61    $false),
% 1.51/0.61    inference(avatar_sat_refutation,[],[f74,f853,f1199,f1711])).
% 1.51/0.61  fof(f1711,plain,(
% 1.51/0.61    spl2_22),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f1710])).
% 1.51/0.61  fof(f1710,plain,(
% 1.51/0.61    $false | spl2_22),
% 1.51/0.61    inference(subsumption_resolution,[],[f1705,f47])).
% 1.51/0.61  fof(f47,plain,(
% 1.51/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.61    inference(equality_resolution,[],[f38])).
% 1.51/0.61  fof(f38,plain,(
% 1.51/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.51/0.61    inference(cnf_transformation,[],[f28])).
% 1.51/0.61  fof(f28,plain,(
% 1.51/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.61    inference(flattening,[],[f27])).
% 1.51/0.61  fof(f27,plain,(
% 1.51/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.61    inference(nnf_transformation,[],[f1])).
% 1.51/0.61  fof(f1,axiom,(
% 1.51/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.61  fof(f1705,plain,(
% 1.51/0.61    ~r1_tarski(sK1,sK1) | spl2_22),
% 1.51/0.61    inference(resolution,[],[f1703,f46])).
% 1.51/0.61  fof(f46,plain,(
% 1.51/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.61    inference(equality_resolution,[],[f39])).
% 1.51/0.61  fof(f39,plain,(
% 1.51/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.51/0.61    inference(cnf_transformation,[],[f28])).
% 1.51/0.61  fof(f1703,plain,(
% 1.51/0.61    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK1,X0)) ) | spl2_22),
% 1.51/0.61    inference(superposition,[],[f1697,f41])).
% 1.51/0.61  fof(f41,plain,(
% 1.51/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f22])).
% 1.51/0.61  fof(f22,plain,(
% 1.51/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.51/0.61    inference(ennf_transformation,[],[f3])).
% 1.51/0.61  fof(f3,axiom,(
% 1.51/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.51/0.61  fof(f1697,plain,(
% 1.51/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),sK1)) ) | spl2_22),
% 1.51/0.61    inference(resolution,[],[f1695,f47])).
% 1.51/0.61  fof(f1695,plain,(
% 1.51/0.61    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r1_tarski(k2_xboole_0(X0,X1),sK1)) ) | spl2_22),
% 1.51/0.61    inference(superposition,[],[f1678,f41])).
% 1.51/0.61  fof(f1678,plain,(
% 1.51/0.61    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_xboole_0(sK1,X0),X1),sK1)) ) | spl2_22),
% 1.51/0.61    inference(resolution,[],[f1221,f35])).
% 1.51/0.61  fof(f35,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.51/0.61    inference(cnf_transformation,[],[f6])).
% 1.51/0.61  fof(f6,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.51/0.61  fof(f1221,plain,(
% 1.51/0.61    ( ! [X4,X5,X3] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X5),X3) | ~r1_tarski(k2_xboole_0(X3,X4),sK1)) ) | spl2_22),
% 1.51/0.61    inference(resolution,[],[f1208,f42])).
% 1.51/0.61  fof(f42,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f23])).
% 1.51/0.61  fof(f23,plain,(
% 1.51/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.51/0.61    inference(ennf_transformation,[],[f2])).
% 1.51/0.61  fof(f2,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.51/0.61  fof(f1208,plain,(
% 1.51/0.61    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(sK0,sK1),X0) | ~r1_tarski(k2_xboole_0(X0,X1),sK1)) ) | spl2_22),
% 1.51/0.61    inference(resolution,[],[f1205,f42])).
% 1.51/0.61  fof(f1205,plain,(
% 1.51/0.61    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(k3_xboole_0(sK0,sK1),X0)) ) | spl2_22),
% 1.51/0.61    inference(superposition,[],[f1203,f41])).
% 1.51/0.61  fof(f1203,plain,(
% 1.51/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),sK1)) ) | spl2_22),
% 1.51/0.61    inference(resolution,[],[f1202,f42])).
% 1.51/0.61  fof(f1202,plain,(
% 1.51/0.61    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_22),
% 1.51/0.61    inference(subsumption_resolution,[],[f1201,f47])).
% 1.51/0.61  fof(f1201,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_22),
% 1.51/0.61    inference(superposition,[],[f1197,f41])).
% 1.51/0.61  fof(f1197,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1)) | spl2_22),
% 1.51/0.61    inference(avatar_component_clause,[],[f1195])).
% 1.51/0.61  fof(f1195,plain,(
% 1.51/0.61    spl2_22 <=> r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1))),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.51/0.61  fof(f1199,plain,(
% 1.51/0.61    ~spl2_22 | spl2_2),
% 1.51/0.61    inference(avatar_split_clause,[],[f1178,f71,f1195])).
% 1.51/0.61  fof(f71,plain,(
% 1.51/0.61    spl2_2 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.51/0.61  fof(f1178,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1)) | spl2_2),
% 1.51/0.61    inference(superposition,[],[f866,f453])).
% 1.51/0.61  fof(f453,plain,(
% 1.51/0.61    ( ! [X2] : (k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X2),sK1)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X2)),k1_relat_1(sK1))) )),
% 1.51/0.61    inference(resolution,[],[f109,f36])).
% 1.51/0.61  fof(f36,plain,(
% 1.51/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f4])).
% 1.51/0.61  fof(f4,axiom,(
% 1.51/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.51/0.61  fof(f109,plain,(
% 1.51/0.61    ( ! [X5] : (~r1_tarski(X5,sK0) | k1_relat_1(k2_xboole_0(X5,sK1)) = k2_xboole_0(k1_relat_1(X5),k1_relat_1(sK1))) )),
% 1.51/0.61    inference(resolution,[],[f51,f52])).
% 1.51/0.61  fof(f52,plain,(
% 1.51/0.61    ( ! [X0] : (v1_relat_1(X0) | ~r1_tarski(X0,sK0)) )),
% 1.51/0.61    inference(resolution,[],[f48,f45])).
% 1.51/0.61  fof(f45,plain,(
% 1.51/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f29])).
% 1.51/0.61  fof(f29,plain,(
% 1.51/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.61    inference(nnf_transformation,[],[f12])).
% 1.51/0.61  fof(f12,axiom,(
% 1.51/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.61  fof(f48,plain,(
% 1.51/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_relat_1(X0)) )),
% 1.51/0.61    inference(resolution,[],[f30,f37])).
% 1.51/0.61  fof(f37,plain,(
% 1.51/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f21])).
% 1.51/0.61  fof(f21,plain,(
% 1.51/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.51/0.61    inference(ennf_transformation,[],[f13])).
% 1.51/0.61  fof(f13,axiom,(
% 1.51/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.51/0.61  fof(f30,plain,(
% 1.51/0.61    v1_relat_1(sK0)),
% 1.51/0.61    inference(cnf_transformation,[],[f26])).
% 1.51/0.61  fof(f26,plain,(
% 1.51/0.61    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.51/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f25,f24])).
% 1.51/0.61  fof(f24,plain,(
% 1.51/0.61    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.51/0.61    introduced(choice_axiom,[])).
% 1.51/0.61  fof(f25,plain,(
% 1.51/0.61    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.51/0.61    introduced(choice_axiom,[])).
% 1.51/0.61  fof(f17,plain,(
% 1.51/0.61    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.51/0.61    inference(ennf_transformation,[],[f16])).
% 1.51/0.61  fof(f16,negated_conjecture,(
% 1.51/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.51/0.61    inference(negated_conjecture,[],[f15])).
% 1.51/0.61  fof(f15,conjecture,(
% 1.51/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 1.51/0.61  fof(f51,plain,(
% 1.51/0.61    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1))) )),
% 1.51/0.61    inference(resolution,[],[f31,f33])).
% 1.51/0.61  fof(f33,plain,(
% 1.51/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f18])).
% 1.51/0.61  fof(f18,plain,(
% 1.51/0.61    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.61    inference(ennf_transformation,[],[f14])).
% 1.51/0.61  fof(f14,axiom,(
% 1.51/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 1.51/0.61  fof(f31,plain,(
% 1.51/0.61    v1_relat_1(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f26])).
% 1.51/0.61  fof(f866,plain,(
% 1.51/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK1))) ) | spl2_2),
% 1.51/0.61    inference(resolution,[],[f73,f42])).
% 1.51/0.61  fof(f73,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | spl2_2),
% 1.51/0.61    inference(avatar_component_clause,[],[f71])).
% 1.51/0.61  fof(f853,plain,(
% 1.51/0.61    spl2_1),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f852])).
% 1.51/0.61  fof(f852,plain,(
% 1.51/0.61    $false | spl2_1),
% 1.51/0.61    inference(subsumption_resolution,[],[f851,f36])).
% 1.51/0.61  fof(f851,plain,(
% 1.51/0.61    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_1),
% 1.51/0.61    inference(subsumption_resolution,[],[f850,f47])).
% 1.51/0.61  fof(f850,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_1),
% 1.51/0.61    inference(superposition,[],[f843,f41])).
% 1.51/0.61  fof(f843,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),k1_relat_1(sK0)) | spl2_1),
% 1.51/0.61    inference(superposition,[],[f75,f350])).
% 1.51/0.61  fof(f350,plain,(
% 1.51/0.61    ( ! [X2] : (k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X2),sK0)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X2)),k1_relat_1(sK0))) )),
% 1.51/0.61    inference(resolution,[],[f95,f36])).
% 1.51/0.61  fof(f95,plain,(
% 1.51/0.61    ( ! [X5] : (~r1_tarski(X5,sK0) | k1_relat_1(k2_xboole_0(X5,sK0)) = k2_xboole_0(k1_relat_1(X5),k1_relat_1(sK0))) )),
% 1.51/0.61    inference(resolution,[],[f49,f52])).
% 1.51/0.61  fof(f49,plain,(
% 1.51/0.61    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X1,sK0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK0))) )),
% 1.51/0.61    inference(resolution,[],[f30,f33])).
% 1.51/0.61  fof(f75,plain,(
% 1.51/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK0))) ) | spl2_1),
% 1.51/0.61    inference(resolution,[],[f69,f42])).
% 1.51/0.61  fof(f69,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | spl2_1),
% 1.51/0.61    inference(avatar_component_clause,[],[f67])).
% 1.51/0.61  fof(f67,plain,(
% 1.51/0.61    spl2_1 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.51/0.61  fof(f74,plain,(
% 1.51/0.61    ~spl2_1 | ~spl2_2),
% 1.51/0.61    inference(avatar_split_clause,[],[f64,f71,f67])).
% 1.51/0.61  fof(f64,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 1.51/0.61    inference(resolution,[],[f32,f34])).
% 1.51/0.61  fof(f34,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f20])).
% 1.51/0.61  fof(f20,plain,(
% 1.51/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.51/0.61    inference(flattening,[],[f19])).
% 1.51/0.61  fof(f19,plain,(
% 1.51/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.51/0.61    inference(ennf_transformation,[],[f5])).
% 1.51/0.61  fof(f5,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.51/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.51/0.61  fof(f32,plain,(
% 1.51/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 1.51/0.61    inference(cnf_transformation,[],[f26])).
% 1.51/0.61  % SZS output end Proof for theBenchmark
% 1.51/0.61  % (2565)------------------------------
% 1.51/0.61  % (2565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.61  % (2565)Termination reason: Refutation
% 1.51/0.61  
% 1.51/0.61  % (2565)Memory used [KB]: 11769
% 1.51/0.61  % (2565)Time elapsed: 0.174 s
% 1.51/0.61  % (2565)------------------------------
% 1.51/0.61  % (2565)------------------------------
% 1.51/0.61  % (2558)Success in time 0.258 s
%------------------------------------------------------------------------------
