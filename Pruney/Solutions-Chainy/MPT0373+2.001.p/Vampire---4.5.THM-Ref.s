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
% DateTime   : Thu Dec  3 12:45:30 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 103 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 197 expanded)
%              Number of equality atoms :   37 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f134,f235])).

fof(f235,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f49,f231])).

fof(f231,plain,
    ( m1_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f30,f143])).

fof(f143,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k6_subset_1(sK0,k6_subset_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f141,f50])).

fof(f50,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f141,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k6_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k6_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f117,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f117,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f62,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f30,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f49,plain,(
    ~ m1_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f27,f48])).

fof(f27,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(X1,X0) )
   => ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f134,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f132,f61,f58])).

fof(f58,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f132,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f113,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f26,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(resolution,[],[f59,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f59,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (795115521)
% 0.13/0.36  ipcrm: permission denied for id (798916610)
% 0.13/0.36  ipcrm: permission denied for id (795148291)
% 0.13/0.36  ipcrm: permission denied for id (798949380)
% 0.13/0.36  ipcrm: permission denied for id (798982149)
% 0.13/0.36  ipcrm: permission denied for id (795246598)
% 0.13/0.37  ipcrm: permission denied for id (799014919)
% 0.13/0.37  ipcrm: permission denied for id (795312136)
% 0.13/0.37  ipcrm: permission denied for id (795344905)
% 0.13/0.37  ipcrm: permission denied for id (795377674)
% 0.13/0.37  ipcrm: permission denied for id (795443212)
% 0.13/0.37  ipcrm: permission denied for id (795475981)
% 0.20/0.38  ipcrm: permission denied for id (795508750)
% 0.20/0.38  ipcrm: permission denied for id (795541519)
% 0.20/0.38  ipcrm: permission denied for id (795574288)
% 0.20/0.38  ipcrm: permission denied for id (795607057)
% 0.20/0.38  ipcrm: permission denied for id (795639826)
% 0.20/0.38  ipcrm: permission denied for id (795672595)
% 0.20/0.38  ipcrm: permission denied for id (795705364)
% 0.20/0.38  ipcrm: permission denied for id (795738133)
% 0.20/0.38  ipcrm: permission denied for id (795770902)
% 0.20/0.39  ipcrm: permission denied for id (795803671)
% 0.20/0.39  ipcrm: permission denied for id (795836440)
% 0.20/0.39  ipcrm: permission denied for id (795869209)
% 0.20/0.39  ipcrm: permission denied for id (795901978)
% 0.20/0.40  ipcrm: permission denied for id (796098591)
% 0.20/0.40  ipcrm: permission denied for id (799244320)
% 0.20/0.40  ipcrm: permission denied for id (799277089)
% 0.20/0.40  ipcrm: permission denied for id (796164130)
% 0.20/0.40  ipcrm: permission denied for id (799309859)
% 0.20/0.40  ipcrm: permission denied for id (799342628)
% 0.20/0.40  ipcrm: permission denied for id (796262437)
% 0.20/0.40  ipcrm: permission denied for id (796327975)
% 0.20/0.41  ipcrm: permission denied for id (796360744)
% 0.20/0.41  ipcrm: permission denied for id (796393513)
% 0.20/0.41  ipcrm: permission denied for id (796426282)
% 0.20/0.41  ipcrm: permission denied for id (796459051)
% 0.20/0.41  ipcrm: permission denied for id (796491820)
% 0.20/0.41  ipcrm: permission denied for id (796524589)
% 0.20/0.41  ipcrm: permission denied for id (796557358)
% 0.20/0.41  ipcrm: permission denied for id (799408175)
% 0.20/0.42  ipcrm: permission denied for id (796622896)
% 0.20/0.42  ipcrm: permission denied for id (799440945)
% 0.20/0.42  ipcrm: permission denied for id (796655667)
% 0.20/0.42  ipcrm: permission denied for id (799539253)
% 0.20/0.42  ipcrm: permission denied for id (799572022)
% 0.20/0.43  ipcrm: permission denied for id (796819512)
% 0.20/0.43  ipcrm: permission denied for id (796852281)
% 0.20/0.43  ipcrm: permission denied for id (796885050)
% 0.20/0.43  ipcrm: permission denied for id (796917819)
% 0.20/0.43  ipcrm: permission denied for id (796950588)
% 0.20/0.43  ipcrm: permission denied for id (797016126)
% 0.20/0.43  ipcrm: permission denied for id (797048895)
% 0.20/0.44  ipcrm: permission denied for id (797081664)
% 0.20/0.44  ipcrm: permission denied for id (799735875)
% 0.20/0.44  ipcrm: permission denied for id (797245509)
% 0.20/0.44  ipcrm: permission denied for id (797311047)
% 0.20/0.44  ipcrm: permission denied for id (799834184)
% 0.20/0.45  ipcrm: permission denied for id (799932491)
% 0.20/0.45  ipcrm: permission denied for id (799998029)
% 0.20/0.45  ipcrm: permission denied for id (797507663)
% 0.20/0.45  ipcrm: permission denied for id (797540432)
% 0.20/0.46  ipcrm: permission denied for id (797573201)
% 0.20/0.46  ipcrm: permission denied for id (800063570)
% 0.20/0.46  ipcrm: permission denied for id (800096339)
% 0.20/0.46  ipcrm: permission denied for id (797671508)
% 0.20/0.46  ipcrm: permission denied for id (800161878)
% 0.20/0.46  ipcrm: permission denied for id (797802584)
% 0.20/0.47  ipcrm: permission denied for id (797835353)
% 0.20/0.47  ipcrm: permission denied for id (800227418)
% 0.20/0.47  ipcrm: permission denied for id (797966429)
% 0.20/0.47  ipcrm: permission denied for id (797999199)
% 0.20/0.47  ipcrm: permission denied for id (798031968)
% 0.20/0.47  ipcrm: permission denied for id (798064737)
% 0.20/0.48  ipcrm: permission denied for id (800358498)
% 0.20/0.48  ipcrm: permission denied for id (798130275)
% 0.20/0.48  ipcrm: permission denied for id (798163044)
% 0.20/0.48  ipcrm: permission denied for id (800424038)
% 0.20/0.48  ipcrm: permission denied for id (800456807)
% 0.20/0.48  ipcrm: permission denied for id (800522345)
% 0.20/0.49  ipcrm: permission denied for id (800587883)
% 0.20/0.49  ipcrm: permission denied for id (798326892)
% 0.20/0.49  ipcrm: permission denied for id (800620653)
% 0.20/0.49  ipcrm: permission denied for id (798359662)
% 0.20/0.49  ipcrm: permission denied for id (800653423)
% 0.20/0.50  ipcrm: permission denied for id (798490738)
% 0.20/0.50  ipcrm: permission denied for id (800751731)
% 0.20/0.50  ipcrm: permission denied for id (800817269)
% 0.20/0.50  ipcrm: permission denied for id (800882807)
% 0.20/0.50  ipcrm: permission denied for id (798687353)
% 0.20/0.50  ipcrm: permission denied for id (798720122)
% 0.20/0.51  ipcrm: permission denied for id (798752891)
% 0.20/0.51  ipcrm: permission denied for id (800948348)
% 0.20/0.51  ipcrm: permission denied for id (798818429)
% 0.20/0.51  ipcrm: permission denied for id (798851198)
% 0.45/0.59  % (6455)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.45/0.60  % (6463)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.45/0.60  % (6455)Refutation found. Thanks to Tanya!
% 0.45/0.60  % SZS status Theorem for theBenchmark
% 0.45/0.60  % SZS output start Proof for theBenchmark
% 0.45/0.60  fof(f238,plain,(
% 0.45/0.60    $false),
% 0.45/0.60    inference(avatar_sat_refutation,[],[f113,f134,f235])).
% 0.45/0.60  fof(f235,plain,(
% 0.45/0.60    ~spl2_2),
% 0.45/0.60    inference(avatar_contradiction_clause,[],[f232])).
% 0.45/0.60  fof(f232,plain,(
% 0.45/0.60    $false | ~spl2_2),
% 0.45/0.60    inference(subsumption_resolution,[],[f49,f231])).
% 0.45/0.60  fof(f231,plain,(
% 0.45/0.60    m1_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.45/0.60    inference(superposition,[],[f30,f143])).
% 0.45/0.60  fof(f143,plain,(
% 0.45/0.60    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k6_subset_1(sK0,k6_subset_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl2_2),
% 0.45/0.60    inference(superposition,[],[f141,f50])).
% 0.45/0.60  fof(f50,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 0.45/0.60    inference(definition_unfolding,[],[f32,f45,f45])).
% 0.45/0.60  fof(f45,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.45/0.60    inference(definition_unfolding,[],[f35,f31,f31])).
% 0.45/0.60  fof(f31,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f13])).
% 0.45/0.60  fof(f13,axiom,(
% 0.45/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.45/0.60  fof(f35,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.45/0.60    inference(cnf_transformation,[],[f5])).
% 0.45/0.60  fof(f5,axiom,(
% 0.45/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.45/0.60  fof(f32,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f1])).
% 0.45/0.60  fof(f1,axiom,(
% 0.45/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.45/0.60  fof(f141,plain,(
% 0.45/0.60    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k6_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k6_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)) | ~spl2_2),
% 0.45/0.60    inference(resolution,[],[f117,f52])).
% 0.45/0.60  fof(f52,plain,(
% 0.45/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 0.45/0.60    inference(definition_unfolding,[],[f40,f45])).
% 0.45/0.60  fof(f40,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f20])).
% 0.45/0.60  fof(f20,plain,(
% 0.45/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.45/0.60    inference(ennf_transformation,[],[f4])).
% 0.45/0.60  fof(f4,axiom,(
% 0.45/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.45/0.60  fof(f117,plain,(
% 0.45/0.60    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_2),
% 0.45/0.60    inference(resolution,[],[f62,f53])).
% 0.45/0.60  fof(f53,plain,(
% 0.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.45/0.60    inference(definition_unfolding,[],[f42,f48])).
% 0.45/0.60  fof(f48,plain,(
% 0.45/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.45/0.60    inference(definition_unfolding,[],[f28,f47])).
% 0.45/0.60  fof(f47,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.45/0.60    inference(definition_unfolding,[],[f33,f46])).
% 0.45/0.60  fof(f46,plain,(
% 0.45/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.45/0.60    inference(definition_unfolding,[],[f43,f44])).
% 0.45/0.60  fof(f44,plain,(
% 0.45/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f9])).
% 0.45/0.60  fof(f9,axiom,(
% 0.45/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.45/0.60  fof(f43,plain,(
% 0.45/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f8])).
% 0.45/0.60  fof(f8,axiom,(
% 0.45/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.45/0.60  fof(f33,plain,(
% 0.45/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f7])).
% 0.45/0.60  fof(f7,axiom,(
% 0.45/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.45/0.60  fof(f28,plain,(
% 0.45/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f6])).
% 0.45/0.60  fof(f6,axiom,(
% 0.45/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.45/0.60  fof(f42,plain,(
% 0.45/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f24])).
% 0.45/0.60  fof(f24,plain,(
% 0.45/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.45/0.60    inference(nnf_transformation,[],[f10])).
% 0.45/0.60  fof(f10,axiom,(
% 0.45/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.45/0.60  fof(f62,plain,(
% 0.45/0.60    r2_hidden(sK1,sK0) | ~spl2_2),
% 0.45/0.60    inference(avatar_component_clause,[],[f61])).
% 0.45/0.60  fof(f61,plain,(
% 0.45/0.60    spl2_2 <=> r2_hidden(sK1,sK0)),
% 0.45/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.45/0.60  fof(f30,plain,(
% 0.45/0.60    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.45/0.60    inference(cnf_transformation,[],[f12])).
% 0.45/0.60  fof(f12,axiom,(
% 0.45/0.60    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.45/0.60  fof(f49,plain,(
% 0.45/0.60    ~m1_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.45/0.60    inference(definition_unfolding,[],[f27,f48])).
% 0.45/0.60  fof(f27,plain,(
% 0.45/0.60    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.45/0.60    inference(cnf_transformation,[],[f22])).
% 0.45/0.60  fof(f22,plain,(
% 0.45/0.60    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0)),
% 0.45/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21])).
% 0.45/0.60  fof(f21,plain,(
% 0.45/0.60    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0)) => (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0))),
% 0.45/0.60    introduced(choice_axiom,[])).
% 0.45/0.60  fof(f17,plain,(
% 0.45/0.60    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0))),
% 0.45/0.60    inference(flattening,[],[f16])).
% 0.45/0.60  fof(f16,plain,(
% 0.45/0.60    ? [X0,X1] : ((~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X1,X0))),
% 0.45/0.60    inference(ennf_transformation,[],[f15])).
% 0.45/0.60  fof(f15,negated_conjecture,(
% 0.45/0.60    ~! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.45/0.60    inference(negated_conjecture,[],[f14])).
% 0.45/0.60  fof(f14,conjecture,(
% 0.45/0.60    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.45/0.60  fof(f134,plain,(
% 0.45/0.60    spl2_1 | spl2_2),
% 0.45/0.60    inference(avatar_split_clause,[],[f132,f61,f58])).
% 0.45/0.60  fof(f58,plain,(
% 0.45/0.60    spl2_1 <=> v1_xboole_0(sK0)),
% 0.45/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.45/0.60  fof(f132,plain,(
% 0.45/0.60    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.45/0.60    inference(resolution,[],[f25,f36])).
% 0.45/0.60  fof(f36,plain,(
% 0.45/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.45/0.60    inference(cnf_transformation,[],[f23])).
% 0.45/0.60  fof(f23,plain,(
% 0.45/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.45/0.60    inference(nnf_transformation,[],[f19])).
% 0.45/0.60  fof(f19,plain,(
% 0.45/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.45/0.60    inference(ennf_transformation,[],[f11])).
% 0.45/0.60  fof(f11,axiom,(
% 0.45/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.45/0.60  fof(f25,plain,(
% 0.45/0.60    m1_subset_1(sK1,sK0)),
% 0.45/0.60    inference(cnf_transformation,[],[f22])).
% 0.45/0.60  fof(f113,plain,(
% 0.45/0.60    ~spl2_1),
% 0.45/0.60    inference(avatar_contradiction_clause,[],[f107])).
% 0.45/0.60  fof(f107,plain,(
% 0.45/0.60    $false | ~spl2_1),
% 0.45/0.60    inference(subsumption_resolution,[],[f26,f105])).
% 0.45/0.60  fof(f105,plain,(
% 0.45/0.60    k1_xboole_0 = sK0 | ~spl2_1),
% 0.45/0.60    inference(resolution,[],[f59,f29])).
% 0.45/0.60  fof(f29,plain,(
% 0.45/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.45/0.60    inference(cnf_transformation,[],[f18])).
% 0.45/0.60  fof(f18,plain,(
% 0.45/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.45/0.60    inference(ennf_transformation,[],[f2])).
% 0.45/0.60  fof(f2,axiom,(
% 0.45/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.45/0.60  fof(f59,plain,(
% 0.45/0.60    v1_xboole_0(sK0) | ~spl2_1),
% 0.45/0.60    inference(avatar_component_clause,[],[f58])).
% 0.45/0.60  fof(f26,plain,(
% 0.45/0.60    k1_xboole_0 != sK0),
% 0.45/0.60    inference(cnf_transformation,[],[f22])).
% 0.45/0.60  % SZS output end Proof for theBenchmark
% 0.45/0.60  % (6455)------------------------------
% 0.45/0.60  % (6455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.60  % (6455)Termination reason: Refutation
% 0.45/0.60  
% 0.45/0.60  % (6455)Memory used [KB]: 10746
% 0.45/0.60  % (6455)Time elapsed: 0.052 s
% 0.45/0.60  % (6455)------------------------------
% 0.45/0.60  % (6455)------------------------------
% 0.45/0.61  % (6319)Success in time 0.253 s
%------------------------------------------------------------------------------
