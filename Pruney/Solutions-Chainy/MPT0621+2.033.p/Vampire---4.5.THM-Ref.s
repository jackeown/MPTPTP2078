%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 115 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  130 ( 455 expanded)
%              Number of equality atoms :   70 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14,f118])).

fof(f118,plain,(
    ! [X2,X1] : X1 = X2 ),
    inference(superposition,[],[f115,f115])).

fof(f115,plain,(
    ! [X0,X1] : k1_funct_1(sK1(sK0),sK3(k1_xboole_0,X1,sK0)) = X0 ),
    inference(subsumption_resolution,[],[f114,f14])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1(sK0),sK3(k1_xboole_0,X1,sK0)) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f95,f67])).

fof(f67,plain,(
    ! [X0] : sK1(sK0) = sK2(sK0,X0) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | sK0 != X2
      | sK2(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f62,f25])).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f62,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK0 != X4
      | ~ v1_relat_1(sK2(X2,X3))
      | sK2(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | ~ v1_funct_1(sK2(X2,X3))
      | sK0 != X4
      | ~ v1_relat_1(sK2(X2,X3))
      | sK2(X2,X3) = sK1(X4) ) ),
    inference(superposition,[],[f55,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | sK0 != X0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f54,f18])).

fof(f18,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f52,f17])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(superposition,[],[f13,f19])).

fof(f19,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f13,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f95,plain,(
    ! [X8,X7,X9] :
      ( k1_funct_1(sK2(X7,X8),sK3(k1_xboole_0,X9,X7)) = X8
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f92,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK2(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X24,X25] :
      ( r2_hidden(sK3(k1_xboole_0,X24,X25),X25)
      | k1_xboole_0 = X25 ) ),
    inference(forward_demodulation,[],[f90,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f90,plain,(
    ! [X24,X25] :
      ( r2_hidden(sK3(k1_xboole_0,X24,X25),X25)
      | k4_xboole_0(k1_xboole_0,X24) = X25 ) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f20,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:10:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (31424)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (31427)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (31426)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (31427)Refutation not found, incomplete strategy% (31427)------------------------------
% 0.22/0.51  % (31427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31427)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31427)Memory used [KB]: 6140
% 0.22/0.51  % (31427)Time elapsed: 0.088 s
% 0.22/0.51  % (31427)------------------------------
% 0.22/0.51  % (31427)------------------------------
% 0.22/0.51  % (31445)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (31435)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (31444)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (31425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (31435)Refutation not found, incomplete strategy% (31435)------------------------------
% 0.22/0.51  % (31435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31435)Memory used [KB]: 6012
% 0.22/0.51  % (31435)Time elapsed: 0.101 s
% 0.22/0.51  % (31435)------------------------------
% 0.22/0.51  % (31435)------------------------------
% 0.22/0.51  % (31442)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (31431)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (31423)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (31430)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (31444)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f14,f118])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X2,X1] : (X1 = X2) )),
% 0.22/0.52    inference(superposition,[],[f115,f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),sK3(k1_xboole_0,X1,sK0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f14])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),sK3(k1_xboole_0,X1,sK0)) = X0 | k1_xboole_0 = sK0) )),
% 0.22/0.52    inference(superposition,[],[f95,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0] : (sK1(sK0) = sK2(sK0,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != X0 | sK2(X0,X1) = sK1(sK0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sK0 != X4 | sK0 != X2 | sK2(X2,X3) = sK1(X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f62,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sK0 != X2 | sK0 != X4 | ~v1_relat_1(sK2(X2,X3)) | sK2(X2,X3) = sK1(X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f59,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sK0 != X2 | ~v1_funct_1(sK2(X2,X3)) | sK0 != X4 | ~v1_relat_1(sK2(X2,X3)) | sK2(X2,X3) = sK1(X4)) )),
% 0.22/0.52    inference(superposition,[],[f55,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | sK0 != X0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f54,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != X0 | ~v1_funct_1(X1) | ~v1_funct_1(sK1(X0)) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f52,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(sK1(X0)) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.22/0.52    inference(superposition,[],[f13,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X8,X7,X9] : (k1_funct_1(sK2(X7,X8),sK3(k1_xboole_0,X9,X7)) = X8 | k1_xboole_0 = X7) )),
% 0.22/0.52    inference(resolution,[],[f92,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK2(X0,X1),X3) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X24,X25] : (r2_hidden(sK3(k1_xboole_0,X24,X25),X25) | k1_xboole_0 = X25) )),
% 0.22/0.52    inference(forward_demodulation,[],[f90,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X24,X25] : (r2_hidden(sK3(k1_xboole_0,X24,X25),X25) | k4_xboole_0(k1_xboole_0,X24) = X25) )),
% 0.22/0.52    inference(resolution,[],[f29,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f20,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (31444)------------------------------
% 0.22/0.52  % (31444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31444)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (31444)Memory used [KB]: 10746
% 0.22/0.52  % (31444)Time elapsed: 0.105 s
% 0.22/0.52  % (31444)------------------------------
% 0.22/0.52  % (31444)------------------------------
% 0.22/0.52  % (31434)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (31439)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (31421)Success in time 0.154 s
%------------------------------------------------------------------------------
