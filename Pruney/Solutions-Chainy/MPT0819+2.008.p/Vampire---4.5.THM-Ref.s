%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 152 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  130 ( 421 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(global_subsumption,[],[f281,f295])).

fof(f295,plain,(
    ~ r2_hidden(sK5(k1_relat_1(sK4),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f21,f266,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f266,plain,(
    ~ r2_hidden(sK5(k1_relat_1(sK4),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f256,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f256,plain,(
    ~ r1_tarski(k1_relat_1(sK4),sK1) ),
    inference(unit_resulting_resolution,[],[f62,f23,f247,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f247,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(unit_resulting_resolution,[],[f22,f244,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f244,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f239,f27])).

fof(f239,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k2_relat_1(sK4),X0),sK2)
      | r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f52,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK4)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f106,f28])).

fof(f28,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f106,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X6),sK4)
      | r2_hidden(X6,sK2) ) ),
    inference(resolution,[],[f44,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f24,f20])).

fof(f20,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP7(sK5(k2_relat_1(X0),X1),X0)
      | r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f26,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP7(X2,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f20,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f281,plain,(
    r2_hidden(sK5(k1_relat_1(sK4),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f261,f102])).

fof(f102,plain,(
    ! [X1] :
      ( ~ sP10(X1,sK4)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f100,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0)
      | ~ sP10(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f100,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK4)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f43,f75])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f261,plain,(
    sP10(sK5(k1_relat_1(sK4),sK1),sK4) ),
    inference(unit_resulting_resolution,[],[f256,f53])).

fof(f53,plain,(
    ! [X2,X3] :
      ( sP10(sK5(k1_relat_1(X2),X3),X2)
      | r1_tarski(k1_relat_1(X2),X3) ) ),
    inference(resolution,[],[f26,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP10(X2,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP10(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (24353)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (24369)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (24376)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (24368)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (24377)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (24360)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.58  % (24366)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (24355)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (24356)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.60  % (24357)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (24377)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 1.95/0.61  % (24367)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.95/0.61  % SZS output start Proof for theBenchmark
% 1.95/0.61  fof(f300,plain,(
% 1.95/0.61    $false),
% 1.95/0.61    inference(global_subsumption,[],[f281,f295])).
% 1.95/0.61  fof(f295,plain,(
% 1.95/0.61    ~r2_hidden(sK5(k1_relat_1(sK4),sK1),sK0)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f21,f266,f25])).
% 1.95/0.61  fof(f25,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f14])).
% 1.95/0.61  fof(f14,plain,(
% 1.95/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.95/0.61    inference(ennf_transformation,[],[f1])).
% 1.95/0.61  fof(f1,axiom,(
% 1.95/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.95/0.61  fof(f266,plain,(
% 1.95/0.61    ~r2_hidden(sK5(k1_relat_1(sK4),sK1),sK1)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f256,f27])).
% 1.95/0.61  fof(f27,plain,(
% 1.95/0.61    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f14])).
% 1.95/0.61  fof(f256,plain,(
% 1.95/0.61    ~r1_tarski(k1_relat_1(sK4),sK1)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f62,f23,f247,f40])).
% 1.95/0.61  fof(f40,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f16])).
% 1.95/0.61  fof(f16,plain,(
% 1.95/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.95/0.61    inference(flattening,[],[f15])).
% 1.95/0.61  fof(f15,plain,(
% 1.95/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.95/0.61    inference(ennf_transformation,[],[f8])).
% 1.95/0.61  fof(f8,axiom,(
% 1.95/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.95/0.61  fof(f247,plain,(
% 1.95/0.61    r1_tarski(k2_relat_1(sK4),sK3)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f22,f244,f42])).
% 1.95/0.61  fof(f42,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f19])).
% 1.95/0.61  fof(f19,plain,(
% 1.95/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.95/0.61    inference(flattening,[],[f18])).
% 1.95/0.61  fof(f18,plain,(
% 1.95/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.95/0.61    inference(ennf_transformation,[],[f2])).
% 1.95/0.61  fof(f2,axiom,(
% 1.95/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.95/0.61  fof(f244,plain,(
% 1.95/0.61    r1_tarski(k2_relat_1(sK4),sK2)),
% 1.95/0.61    inference(duplicate_literal_removal,[],[f242])).
% 1.95/0.61  fof(f242,plain,(
% 1.95/0.61    r1_tarski(k2_relat_1(sK4),sK2) | r1_tarski(k2_relat_1(sK4),sK2)),
% 1.95/0.61    inference(resolution,[],[f239,f27])).
% 1.95/0.61  fof(f239,plain,(
% 1.95/0.61    ( ! [X0] : (r2_hidden(sK5(k2_relat_1(sK4),X0),sK2) | r1_tarski(k2_relat_1(sK4),X0)) )),
% 1.95/0.61    inference(resolution,[],[f52,f107])).
% 1.95/0.61  fof(f107,plain,(
% 1.95/0.61    ( ! [X0] : (~sP7(X0,sK4) | r2_hidden(X0,sK2)) )),
% 1.95/0.61    inference(resolution,[],[f106,f28])).
% 1.95/0.61  fof(f28,plain,(
% 1.95/0.61    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK8(X0,X2),X2),X0) | ~sP7(X2,X0)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f6])).
% 1.95/0.61  fof(f6,axiom,(
% 1.95/0.61    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.95/0.61  fof(f106,plain,(
% 1.95/0.61    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X7,X6),sK4) | r2_hidden(X6,sK2)) )),
% 1.95/0.61    inference(resolution,[],[f44,f75])).
% 1.95/0.61  fof(f75,plain,(
% 1.95/0.61    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,sK4)) )),
% 1.95/0.61    inference(resolution,[],[f24,f20])).
% 1.95/0.61  fof(f20,plain,(
% 1.95/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.95/0.61    inference(cnf_transformation,[],[f12])).
% 1.95/0.61  fof(f12,plain,(
% 1.95/0.61    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.95/0.61    inference(flattening,[],[f11])).
% 1.95/0.61  fof(f11,plain,(
% 1.95/0.61    ? [X0,X1,X2,X3,X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.95/0.61    inference(ennf_transformation,[],[f10])).
% 1.95/0.61  fof(f10,negated_conjecture,(
% 1.95/0.61    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 1.95/0.61    inference(negated_conjecture,[],[f9])).
% 1.95/0.61  fof(f9,conjecture,(
% 1.95/0.61    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).
% 1.95/0.61  fof(f24,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f13])).
% 1.95/0.61  fof(f13,plain,(
% 1.95/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.95/0.61    inference(ennf_transformation,[],[f4])).
% 1.95/0.61  fof(f4,axiom,(
% 1.95/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.95/0.61  fof(f44,plain,(
% 1.95/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f3])).
% 1.95/0.61  fof(f3,axiom,(
% 1.95/0.61    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.95/0.61  fof(f52,plain,(
% 1.95/0.61    ( ! [X0,X1] : (sP7(sK5(k2_relat_1(X0),X1),X0) | r1_tarski(k2_relat_1(X0),X1)) )),
% 1.95/0.61    inference(resolution,[],[f26,f46])).
% 1.95/0.61  fof(f46,plain,(
% 1.95/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP7(X2,X0)) )),
% 1.95/0.61    inference(equality_resolution,[],[f31])).
% 1.95/0.61  fof(f31,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (sP7(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.95/0.61    inference(cnf_transformation,[],[f6])).
% 1.95/0.61  fof(f26,plain,(
% 1.95/0.61    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f14])).
% 1.95/0.61  fof(f22,plain,(
% 1.95/0.61    r1_tarski(sK2,sK3)),
% 1.95/0.61    inference(cnf_transformation,[],[f12])).
% 1.95/0.61  fof(f23,plain,(
% 1.95/0.61    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.95/0.61    inference(cnf_transformation,[],[f12])).
% 1.95/0.61  fof(f62,plain,(
% 1.95/0.61    v1_relat_1(sK4)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f20,f41])).
% 1.95/0.61  fof(f41,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f17])).
% 1.95/0.61  fof(f17,plain,(
% 1.95/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.61    inference(ennf_transformation,[],[f7])).
% 1.95/0.61  fof(f7,axiom,(
% 1.95/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.95/0.61  fof(f21,plain,(
% 1.95/0.61    r1_tarski(sK0,sK1)),
% 1.95/0.61    inference(cnf_transformation,[],[f12])).
% 1.95/0.61  fof(f281,plain,(
% 1.95/0.61    r2_hidden(sK5(k1_relat_1(sK4),sK1),sK0)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f261,f102])).
% 1.95/0.61  fof(f102,plain,(
% 1.95/0.61    ( ! [X1] : (~sP10(X1,sK4) | r2_hidden(X1,sK0)) )),
% 1.95/0.61    inference(resolution,[],[f100,f34])).
% 1.95/0.61  fof(f34,plain,(
% 1.95/0.61    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0) | ~sP10(X2,X0)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f5])).
% 1.95/0.61  fof(f5,axiom,(
% 1.95/0.61    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.95/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.95/0.61  fof(f100,plain,(
% 1.95/0.61    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),sK4) | r2_hidden(X6,sK0)) )),
% 1.95/0.61    inference(resolution,[],[f43,f75])).
% 1.95/0.61  fof(f43,plain,(
% 1.95/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.95/0.61    inference(cnf_transformation,[],[f3])).
% 1.95/0.61  fof(f261,plain,(
% 1.95/0.61    sP10(sK5(k1_relat_1(sK4),sK1),sK4)),
% 1.95/0.61    inference(unit_resulting_resolution,[],[f256,f53])).
% 1.95/0.61  fof(f53,plain,(
% 1.95/0.61    ( ! [X2,X3] : (sP10(sK5(k1_relat_1(X2),X3),X2) | r1_tarski(k1_relat_1(X2),X3)) )),
% 1.95/0.61    inference(resolution,[],[f26,f48])).
% 1.95/0.61  fof(f48,plain,(
% 1.95/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | sP10(X2,X0)) )),
% 1.95/0.61    inference(equality_resolution,[],[f37])).
% 1.95/0.61  fof(f37,plain,(
% 1.95/0.61    ( ! [X2,X0,X1] : (sP10(X2,X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.95/0.61    inference(cnf_transformation,[],[f5])).
% 1.95/0.61  % SZS output end Proof for theBenchmark
% 1.95/0.61  % (24377)------------------------------
% 1.95/0.61  % (24377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.61  % (24377)Termination reason: Refutation
% 1.95/0.61  
% 1.95/0.61  % (24377)Memory used [KB]: 6652
% 1.95/0.61  % (24377)Time elapsed: 0.163 s
% 1.95/0.61  % (24377)------------------------------
% 1.95/0.61  % (24377)------------------------------
% 1.95/0.61  % (24358)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.95/0.61  % (24352)Success in time 0.251 s
%------------------------------------------------------------------------------
