%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   34 (  76 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   93 ( 305 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X0,k2_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK0,k2_relat_1(sK1))
          & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r2_hidden(sK0,k2_relat_1(sK1))
        & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1)))
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(sK0,k2_relat_1(sK1))
      & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(f59,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f20])).

fof(f20,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(k5_relat_1(X0,sK1)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f49,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(k5_relat_1(X0,sK1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f47,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(sK0,k9_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f46,f26])).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f46,plain,(
    ! [X0] : ~ r2_hidden(sK0,k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(subsumption_resolution,[],[f44,f18])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_relat_1(k7_relat_1(sK1,X0)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f21,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f21,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:16:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1224933376)
% 0.21/0.37  ipcrm: permission denied for id (1225752577)
% 0.21/0.37  ipcrm: permission denied for id (1229586435)
% 0.21/0.37  ipcrm: permission denied for id (1229651973)
% 0.21/0.37  ipcrm: permission denied for id (1224998918)
% 0.21/0.38  ipcrm: permission denied for id (1225916423)
% 0.21/0.38  ipcrm: permission denied for id (1231552521)
% 0.21/0.38  ipcrm: permission denied for id (1226014730)
% 0.21/0.38  ipcrm: permission denied for id (1226047499)
% 0.21/0.38  ipcrm: permission denied for id (1229750284)
% 0.21/0.38  ipcrm: permission denied for id (1231585293)
% 0.21/0.38  ipcrm: permission denied for id (1231618062)
% 0.21/0.39  ipcrm: permission denied for id (1231650831)
% 0.21/0.39  ipcrm: permission denied for id (1231716369)
% 0.21/0.39  ipcrm: permission denied for id (1226276882)
% 0.21/0.39  ipcrm: permission denied for id (1225064468)
% 0.21/0.39  ipcrm: permission denied for id (1226342421)
% 0.21/0.39  ipcrm: permission denied for id (1225097238)
% 0.21/0.40  ipcrm: permission denied for id (1230012439)
% 0.21/0.40  ipcrm: permission denied for id (1230045208)
% 0.21/0.40  ipcrm: permission denied for id (1226440729)
% 0.21/0.40  ipcrm: permission denied for id (1230077978)
% 0.21/0.40  ipcrm: permission denied for id (1230110747)
% 0.21/0.40  ipcrm: permission denied for id (1230143516)
% 0.21/0.40  ipcrm: permission denied for id (1226571805)
% 0.21/0.40  ipcrm: permission denied for id (1230176286)
% 0.21/0.41  ipcrm: permission denied for id (1231781919)
% 0.21/0.41  ipcrm: permission denied for id (1226670112)
% 0.21/0.41  ipcrm: permission denied for id (1231814689)
% 0.21/0.41  ipcrm: permission denied for id (1225162786)
% 0.21/0.41  ipcrm: permission denied for id (1230274595)
% 0.21/0.41  ipcrm: permission denied for id (1226801189)
% 0.21/0.41  ipcrm: permission denied for id (1230372902)
% 0.21/0.41  ipcrm: permission denied for id (1226866727)
% 0.21/0.42  ipcrm: permission denied for id (1231880232)
% 0.21/0.42  ipcrm: permission denied for id (1231913001)
% 0.21/0.42  ipcrm: permission denied for id (1226965034)
% 0.21/0.42  ipcrm: permission denied for id (1227030572)
% 0.21/0.42  ipcrm: permission denied for id (1227063341)
% 0.21/0.42  ipcrm: permission denied for id (1227096110)
% 0.21/0.43  ipcrm: permission denied for id (1230503983)
% 0.21/0.43  ipcrm: permission denied for id (1227161648)
% 0.21/0.43  ipcrm: permission denied for id (1225228337)
% 0.21/0.43  ipcrm: permission denied for id (1232044084)
% 0.21/0.43  ipcrm: permission denied for id (1227292725)
% 0.21/0.43  ipcrm: permission denied for id (1227325494)
% 0.21/0.43  ipcrm: permission denied for id (1227358263)
% 0.21/0.44  ipcrm: permission denied for id (1227391032)
% 0.21/0.44  ipcrm: permission denied for id (1230635065)
% 0.21/0.44  ipcrm: permission denied for id (1227456570)
% 0.21/0.44  ipcrm: permission denied for id (1227489339)
% 0.21/0.44  ipcrm: permission denied for id (1227522108)
% 0.21/0.44  ipcrm: permission denied for id (1230667837)
% 0.21/0.44  ipcrm: permission denied for id (1227587646)
% 0.21/0.44  ipcrm: permission denied for id (1230700607)
% 0.21/0.45  ipcrm: permission denied for id (1227685952)
% 0.21/0.45  ipcrm: permission denied for id (1227718721)
% 0.21/0.45  ipcrm: permission denied for id (1227751490)
% 0.21/0.45  ipcrm: permission denied for id (1230733379)
% 0.21/0.45  ipcrm: permission denied for id (1230766148)
% 0.21/0.45  ipcrm: permission denied for id (1230798917)
% 0.21/0.45  ipcrm: permission denied for id (1227882566)
% 0.21/0.45  ipcrm: permission denied for id (1227915335)
% 0.21/0.46  ipcrm: permission denied for id (1227948104)
% 0.21/0.46  ipcrm: permission denied for id (1227980873)
% 0.21/0.46  ipcrm: permission denied for id (1230831690)
% 0.21/0.46  ipcrm: permission denied for id (1225261131)
% 0.21/0.46  ipcrm: permission denied for id (1228111950)
% 0.21/0.47  ipcrm: permission denied for id (1225293904)
% 0.21/0.47  ipcrm: permission denied for id (1232175185)
% 0.21/0.47  ipcrm: permission denied for id (1225359442)
% 0.21/0.47  ipcrm: permission denied for id (1230995539)
% 0.21/0.47  ipcrm: permission denied for id (1228275796)
% 0.21/0.47  ipcrm: permission denied for id (1232207957)
% 0.21/0.47  ipcrm: permission denied for id (1228341334)
% 0.21/0.47  ipcrm: permission denied for id (1228374103)
% 0.21/0.48  ipcrm: permission denied for id (1232240728)
% 0.21/0.48  ipcrm: permission denied for id (1228439641)
% 0.21/0.48  ipcrm: permission denied for id (1228472410)
% 0.21/0.48  ipcrm: permission denied for id (1228505179)
% 0.21/0.48  ipcrm: permission denied for id (1228537948)
% 0.21/0.48  ipcrm: permission denied for id (1225457758)
% 0.21/0.48  ipcrm: permission denied for id (1228603487)
% 0.21/0.48  ipcrm: permission denied for id (1228636256)
% 0.21/0.49  ipcrm: permission denied for id (1232306273)
% 0.21/0.49  ipcrm: permission denied for id (1225490530)
% 0.21/0.49  ipcrm: permission denied for id (1228701795)
% 0.21/0.49  ipcrm: permission denied for id (1228734564)
% 0.21/0.49  ipcrm: permission denied for id (1232339045)
% 0.21/0.49  ipcrm: permission denied for id (1228800102)
% 0.21/0.49  ipcrm: permission denied for id (1225556071)
% 0.21/0.49  ipcrm: permission denied for id (1228832872)
% 0.21/0.50  ipcrm: permission denied for id (1228865641)
% 0.21/0.50  ipcrm: permission denied for id (1228898410)
% 0.21/0.50  ipcrm: permission denied for id (1228931179)
% 0.21/0.50  ipcrm: permission denied for id (1228963948)
% 0.21/0.50  ipcrm: permission denied for id (1229029486)
% 0.21/0.50  ipcrm: permission denied for id (1229062255)
% 0.21/0.50  ipcrm: permission denied for id (1229095024)
% 0.21/0.50  ipcrm: permission denied for id (1229127793)
% 0.21/0.51  ipcrm: permission denied for id (1231224946)
% 0.21/0.51  ipcrm: permission denied for id (1225621619)
% 0.21/0.51  ipcrm: permission denied for id (1229193332)
% 0.21/0.51  ipcrm: permission denied for id (1229226101)
% 0.21/0.51  ipcrm: permission denied for id (1225654390)
% 0.21/0.51  ipcrm: permission denied for id (1231323255)
% 0.21/0.51  ipcrm: permission denied for id (1229291640)
% 0.21/0.51  ipcrm: permission denied for id (1229324409)
% 0.21/0.52  ipcrm: permission denied for id (1229357178)
% 0.21/0.52  ipcrm: permission denied for id (1232404603)
% 0.21/0.52  ipcrm: permission denied for id (1231356028)
% 0.21/0.52  ipcrm: permission denied for id (1231388797)
% 0.21/0.52  ipcrm: permission denied for id (1229488254)
% 0.21/0.52  ipcrm: permission denied for id (1231421567)
% 1.15/0.66  % (14724)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.15/0.67  % (14738)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.15/0.67  % (14742)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.15/0.68  % (14731)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.15/0.68  % (14724)Refutation found. Thanks to Tanya!
% 1.15/0.68  % SZS status Theorem for theBenchmark
% 1.15/0.68  % SZS output start Proof for theBenchmark
% 1.15/0.68  fof(f61,plain,(
% 1.15/0.68    $false),
% 1.15/0.68    inference(subsumption_resolution,[],[f59,f19])).
% 1.15/0.68  fof(f19,plain,(
% 1.15/0.68    v1_relat_1(sK2)),
% 1.15/0.68    inference(cnf_transformation,[],[f17])).
% 1.15/0.68  fof(f17,plain,(
% 1.15/0.68    (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 1.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).
% 1.15/0.68  fof(f15,plain,(
% 1.15/0.68    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.15/0.68    introduced(choice_axiom,[])).
% 1.15/0.68  fof(f16,plain,(
% 1.15/0.68    ? [X2] : (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1))) & v1_relat_1(X2)) => (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 1.15/0.68    introduced(choice_axiom,[])).
% 1.15/0.68  fof(f10,plain,(
% 1.15/0.68    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 1.15/0.68    inference(flattening,[],[f9])).
% 1.15/0.68  fof(f9,plain,(
% 1.15/0.68    ? [X0,X1] : (? [X2] : ((~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 1.15/0.68    inference(ennf_transformation,[],[f8])).
% 1.15/0.68  fof(f8,plain,(
% 1.15/0.68    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 1.15/0.68    inference(pure_predicate_removal,[],[f6])).
% 1.15/0.68  fof(f6,negated_conjecture,(
% 1.15/0.68    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 1.15/0.68    inference(negated_conjecture,[],[f5])).
% 1.15/0.68  fof(f5,conjecture,(
% 1.15/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 1.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).
% 1.15/0.68  fof(f59,plain,(
% 1.15/0.68    ~v1_relat_1(sK2)),
% 1.15/0.68    inference(resolution,[],[f50,f20])).
% 1.15/0.68  fof(f20,plain,(
% 1.15/0.68    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 1.15/0.68    inference(cnf_transformation,[],[f17])).
% 1.15/0.68  fof(f50,plain,(
% 1.15/0.68    ( ! [X0] : (~r2_hidden(sK0,k2_relat_1(k5_relat_1(X0,sK1))) | ~v1_relat_1(X0)) )),
% 1.15/0.68    inference(subsumption_resolution,[],[f49,f18])).
% 1.15/0.68  fof(f18,plain,(
% 1.15/0.68    v1_relat_1(sK1)),
% 1.15/0.68    inference(cnf_transformation,[],[f17])).
% 1.15/0.68  fof(f49,plain,(
% 1.15/0.68    ( ! [X0] : (~r2_hidden(sK0,k2_relat_1(k5_relat_1(X0,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 1.15/0.68    inference(superposition,[],[f47,f23])).
% 1.15/0.68  fof(f23,plain,(
% 1.15/0.68    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.15/0.68    inference(cnf_transformation,[],[f12])).
% 1.15/0.68  fof(f12,plain,(
% 1.15/0.68    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.15/0.68    inference(ennf_transformation,[],[f3])).
% 1.15/0.68  fof(f3,axiom,(
% 1.15/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.15/0.68  fof(f47,plain,(
% 1.15/0.68    ( ! [X0] : (~r2_hidden(sK0,k9_relat_1(sK1,X0))) )),
% 1.15/0.68    inference(forward_demodulation,[],[f46,f26])).
% 1.15/0.68  fof(f26,plain,(
% 1.15/0.68    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 1.15/0.68    inference(resolution,[],[f18,f25])).
% 1.15/0.68  fof(f25,plain,(
% 1.15/0.68    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.15/0.68    inference(cnf_transformation,[],[f14])).
% 1.15/0.68  fof(f14,plain,(
% 1.15/0.68    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.15/0.68    inference(ennf_transformation,[],[f2])).
% 1.15/0.68  fof(f2,axiom,(
% 1.15/0.68    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.15/0.68  fof(f46,plain,(
% 1.15/0.68    ( ! [X0] : (~r2_hidden(sK0,k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.15/0.68    inference(subsumption_resolution,[],[f44,f18])).
% 1.15/0.68  fof(f44,plain,(
% 1.15/0.68    ( ! [X0] : (~r2_hidden(sK0,k2_relat_1(k7_relat_1(sK1,X0))) | ~v1_relat_1(sK1)) )),
% 1.15/0.68    inference(resolution,[],[f36,f24])).
% 1.15/0.68  fof(f24,plain,(
% 1.15/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.15/0.68    inference(cnf_transformation,[],[f13])).
% 1.15/0.68  fof(f13,plain,(
% 1.15/0.68    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.15/0.68    inference(ennf_transformation,[],[f4])).
% 1.15/0.68  fof(f4,axiom,(
% 1.15/0.68    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 1.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 1.15/0.68  fof(f36,plain,(
% 1.15/0.68    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | ~r2_hidden(sK0,X0)) )),
% 1.15/0.68    inference(resolution,[],[f21,f22])).
% 1.15/0.68  fof(f22,plain,(
% 1.15/0.68    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.15/0.68    inference(cnf_transformation,[],[f11])).
% 1.15/0.68  fof(f11,plain,(
% 1.15/0.68    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.15/0.68    inference(ennf_transformation,[],[f7])).
% 1.15/0.68  fof(f7,plain,(
% 1.15/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.15/0.68    inference(unused_predicate_definition_removal,[],[f1])).
% 1.15/0.68  fof(f1,axiom,(
% 1.15/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.15/0.68  fof(f21,plain,(
% 1.15/0.68    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.15/0.68    inference(cnf_transformation,[],[f17])).
% 1.15/0.68  % SZS output end Proof for theBenchmark
% 1.15/0.68  % (14724)------------------------------
% 1.15/0.68  % (14724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.68  % (14724)Termination reason: Refutation
% 1.15/0.68  
% 1.15/0.68  % (14724)Memory used [KB]: 1791
% 1.15/0.68  % (14724)Time elapsed: 0.098 s
% 1.15/0.68  % (14724)------------------------------
% 1.15/0.68  % (14724)------------------------------
% 1.15/0.68  % (14735)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.15/0.68  % (14567)Success in time 0.322 s
%------------------------------------------------------------------------------
