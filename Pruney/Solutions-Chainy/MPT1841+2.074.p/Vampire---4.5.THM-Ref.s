%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:19 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   42 (  79 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 305 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f22])).

fof(f22,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f46,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f45,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f42,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f41,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_tarski(sK1)) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f37,f22])).

fof(f37,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f36,f23])).

fof(f36,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f24,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:42:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1214349313)
% 0.21/0.37  ipcrm: permission denied for id (1217921026)
% 0.21/0.37  ipcrm: permission denied for id (1217953795)
% 0.21/0.37  ipcrm: permission denied for id (1220804612)
% 0.21/0.38  ipcrm: permission denied for id (1218019333)
% 0.21/0.38  ipcrm: permission denied for id (1214513158)
% 0.21/0.38  ipcrm: permission denied for id (1218052103)
% 0.21/0.38  ipcrm: permission denied for id (1223000072)
% 0.21/0.38  ipcrm: permission denied for id (1220902921)
% 0.21/0.38  ipcrm: permission denied for id (1220935690)
% 0.21/0.38  ipcrm: permission denied for id (1220968459)
% 0.21/0.38  ipcrm: permission denied for id (1218215948)
% 0.21/0.39  ipcrm: permission denied for id (1214709773)
% 0.21/0.39  ipcrm: permission denied for id (1214742542)
% 0.21/0.39  ipcrm: permission denied for id (1218248719)
% 0.21/0.39  ipcrm: permission denied for id (1218281488)
% 0.21/0.39  ipcrm: permission denied for id (1222377489)
% 0.21/0.39  ipcrm: permission denied for id (1218347026)
% 0.21/0.39  ipcrm: permission denied for id (1218379795)
% 0.21/0.39  ipcrm: permission denied for id (1222410260)
% 0.21/0.40  ipcrm: permission denied for id (1218445333)
% 0.21/0.40  ipcrm: permission denied for id (1214939158)
% 0.21/0.40  ipcrm: permission denied for id (1218478103)
% 0.21/0.40  ipcrm: permission denied for id (1218510872)
% 0.21/0.40  ipcrm: permission denied for id (1221066777)
% 0.21/0.40  ipcrm: permission denied for id (1215070234)
% 0.21/0.40  ipcrm: permission denied for id (1218576411)
% 0.21/0.40  ipcrm: permission denied for id (1215103004)
% 0.21/0.41  ipcrm: permission denied for id (1218609181)
% 0.21/0.41  ipcrm: permission denied for id (1221099550)
% 0.21/0.41  ipcrm: permission denied for id (1218674719)
% 0.21/0.41  ipcrm: permission denied for id (1215234080)
% 0.21/0.41  ipcrm: permission denied for id (1218707489)
% 0.21/0.41  ipcrm: permission denied for id (1218740258)
% 0.21/0.41  ipcrm: permission denied for id (1222443043)
% 0.21/0.41  ipcrm: permission denied for id (1221165092)
% 0.21/0.42  ipcrm: permission denied for id (1222475813)
% 0.21/0.42  ipcrm: permission denied for id (1215365158)
% 0.21/0.42  ipcrm: permission denied for id (1218871335)
% 0.21/0.42  ipcrm: permission denied for id (1218904104)
% 0.21/0.42  ipcrm: permission denied for id (1218936873)
% 0.21/0.42  ipcrm: permission denied for id (1218969642)
% 0.21/0.42  ipcrm: permission denied for id (1215463467)
% 0.21/0.42  ipcrm: permission denied for id (1221230636)
% 0.21/0.43  ipcrm: permission denied for id (1221263405)
% 0.21/0.43  ipcrm: permission denied for id (1215561774)
% 0.21/0.43  ipcrm: permission denied for id (1223295023)
% 0.21/0.43  ipcrm: permission denied for id (1219133488)
% 0.21/0.43  ipcrm: permission denied for id (1221328945)
% 0.21/0.43  ipcrm: permission denied for id (1215692850)
% 0.21/0.43  ipcrm: permission denied for id (1215725619)
% 0.21/0.43  ipcrm: permission denied for id (1223065652)
% 0.21/0.44  ipcrm: permission denied for id (1223327797)
% 0.21/0.44  ipcrm: permission denied for id (1221427254)
% 0.21/0.44  ipcrm: permission denied for id (1215823927)
% 0.21/0.44  ipcrm: permission denied for id (1215856696)
% 0.21/0.44  ipcrm: permission denied for id (1219297337)
% 0.21/0.44  ipcrm: permission denied for id (1219330106)
% 0.21/0.44  ipcrm: permission denied for id (1215955003)
% 0.21/0.44  ipcrm: permission denied for id (1215987772)
% 0.21/0.45  ipcrm: permission denied for id (1221460029)
% 0.21/0.45  ipcrm: permission denied for id (1216020542)
% 0.21/0.45  ipcrm: permission denied for id (1222606911)
% 0.21/0.45  ipcrm: permission denied for id (1222639680)
% 0.21/0.45  ipcrm: permission denied for id (1216118849)
% 0.21/0.45  ipcrm: permission denied for id (1216151618)
% 0.21/0.45  ipcrm: permission denied for id (1216184387)
% 0.21/0.45  ipcrm: permission denied for id (1221558340)
% 0.21/0.46  ipcrm: permission denied for id (1216249925)
% 0.21/0.46  ipcrm: permission denied for id (1216282694)
% 0.21/0.46  ipcrm: permission denied for id (1216315463)
% 0.21/0.46  ipcrm: permission denied for id (1219526728)
% 0.21/0.46  ipcrm: permission denied for id (1219559497)
% 0.21/0.46  ipcrm: permission denied for id (1222672458)
% 0.21/0.46  ipcrm: permission denied for id (1219625035)
% 0.21/0.46  ipcrm: permission denied for id (1216413772)
% 0.21/0.47  ipcrm: permission denied for id (1216446541)
% 0.21/0.47  ipcrm: permission denied for id (1222705230)
% 0.21/0.47  ipcrm: permission denied for id (1221656655)
% 0.21/0.47  ipcrm: permission denied for id (1221689424)
% 0.21/0.47  ipcrm: permission denied for id (1216577617)
% 0.21/0.47  ipcrm: permission denied for id (1221722194)
% 0.21/0.47  ipcrm: permission denied for id (1216643155)
% 0.21/0.47  ipcrm: permission denied for id (1219788884)
% 0.21/0.48  ipcrm: permission denied for id (1221754965)
% 0.21/0.48  ipcrm: permission denied for id (1221787734)
% 0.21/0.48  ipcrm: permission denied for id (1223131223)
% 0.21/0.48  ipcrm: permission denied for id (1219919960)
% 0.21/0.48  ipcrm: permission denied for id (1219952729)
% 0.21/0.48  ipcrm: permission denied for id (1219985498)
% 0.21/0.48  ipcrm: permission denied for id (1216872539)
% 0.21/0.48  ipcrm: permission denied for id (1221853276)
% 0.21/0.49  ipcrm: permission denied for id (1223163997)
% 0.21/0.49  ipcrm: permission denied for id (1220083806)
% 0.21/0.49  ipcrm: permission denied for id (1216970847)
% 0.21/0.49  ipcrm: permission denied for id (1217003616)
% 0.21/0.49  ipcrm: permission denied for id (1220116577)
% 0.21/0.49  ipcrm: permission denied for id (1220149346)
% 0.21/0.49  ipcrm: permission denied for id (1220182115)
% 0.21/0.49  ipcrm: permission denied for id (1217101924)
% 0.21/0.50  ipcrm: permission denied for id (1221918821)
% 0.21/0.50  ipcrm: permission denied for id (1221951590)
% 0.21/0.50  ipcrm: permission denied for id (1220280423)
% 0.21/0.50  ipcrm: permission denied for id (1222803560)
% 0.21/0.50  ipcrm: permission denied for id (1222017129)
% 0.21/0.50  ipcrm: permission denied for id (1222049898)
% 0.21/0.50  ipcrm: permission denied for id (1217298539)
% 0.21/0.50  ipcrm: permission denied for id (1217331308)
% 0.21/0.51  ipcrm: permission denied for id (1217364077)
% 0.21/0.51  ipcrm: permission denied for id (1217396846)
% 0.21/0.51  ipcrm: permission denied for id (1220411503)
% 0.21/0.51  ipcrm: permission denied for id (1222082672)
% 0.21/0.51  ipcrm: permission denied for id (1222115441)
% 0.21/0.51  ipcrm: permission denied for id (1217495154)
% 0.21/0.51  ipcrm: permission denied for id (1222148211)
% 0.21/0.51  ipcrm: permission denied for id (1222180980)
% 0.21/0.52  ipcrm: permission denied for id (1222836341)
% 0.21/0.52  ipcrm: permission denied for id (1220608118)
% 0.21/0.52  ipcrm: permission denied for id (1217626231)
% 0.21/0.52  ipcrm: permission denied for id (1220640888)
% 0.21/0.52  ipcrm: permission denied for id (1217691769)
% 0.21/0.52  ipcrm: permission denied for id (1217724538)
% 0.21/0.52  ipcrm: permission denied for id (1223196795)
% 0.21/0.52  ipcrm: permission denied for id (1217790076)
% 0.21/0.53  ipcrm: permission denied for id (1217822845)
% 0.21/0.53  ipcrm: permission denied for id (1220706430)
% 0.85/0.64  % (4149)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.85/0.65  % (4149)Refutation found. Thanks to Tanya!
% 0.85/0.65  % SZS status Theorem for theBenchmark
% 0.85/0.65  % SZS output start Proof for theBenchmark
% 0.85/0.65  fof(f47,plain,(
% 0.85/0.65    $false),
% 0.85/0.65    inference(subsumption_resolution,[],[f46,f22])).
% 0.85/0.65  fof(f22,plain,(
% 0.85/0.65    ~v1_xboole_0(sK0)),
% 0.85/0.65    inference(cnf_transformation,[],[f20])).
% 0.85/0.65  fof(f20,plain,(
% 0.85/0.65    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.85/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).
% 0.85/0.65  fof(f18,plain,(
% 0.85/0.65    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.85/0.65    introduced(choice_axiom,[])).
% 0.85/0.65  fof(f19,plain,(
% 0.85/0.65    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.85/0.65    introduced(choice_axiom,[])).
% 0.85/0.65  fof(f10,plain,(
% 0.85/0.65    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.85/0.65    inference(flattening,[],[f9])).
% 0.85/0.65  fof(f9,plain,(
% 0.85/0.65    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.85/0.65    inference(ennf_transformation,[],[f8])).
% 0.85/0.65  fof(f8,negated_conjecture,(
% 0.85/0.65    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.85/0.65    inference(negated_conjecture,[],[f7])).
% 0.85/0.65  fof(f7,conjecture,(
% 0.85/0.65    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.85/0.65  fof(f46,plain,(
% 0.85/0.65    v1_xboole_0(sK0)),
% 0.85/0.65    inference(subsumption_resolution,[],[f45,f23])).
% 0.85/0.65  fof(f23,plain,(
% 0.85/0.65    m1_subset_1(sK1,sK0)),
% 0.85/0.65    inference(cnf_transformation,[],[f20])).
% 0.85/0.65  fof(f45,plain,(
% 0.85/0.65    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.85/0.65    inference(resolution,[],[f43,f29])).
% 0.85/0.65  fof(f29,plain,(
% 0.85/0.65    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.85/0.65    inference(cnf_transformation,[],[f21])).
% 0.85/0.65  fof(f21,plain,(
% 0.85/0.65    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.85/0.65    inference(nnf_transformation,[],[f14])).
% 0.85/0.65  fof(f14,plain,(
% 0.85/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.85/0.65    inference(ennf_transformation,[],[f2])).
% 0.85/0.65  fof(f2,axiom,(
% 0.85/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.85/0.65  fof(f43,plain,(
% 0.85/0.65    ~r2_hidden(sK1,sK0)),
% 0.85/0.65    inference(resolution,[],[f42,f33])).
% 0.85/0.65  fof(f33,plain,(
% 0.85/0.65    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.85/0.65    inference(cnf_transformation,[],[f15])).
% 0.85/0.65  fof(f15,plain,(
% 0.85/0.65    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.85/0.65    inference(ennf_transformation,[],[f3])).
% 0.85/0.65  fof(f3,axiom,(
% 0.85/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.85/0.65  fof(f42,plain,(
% 0.85/0.65    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.85/0.65    inference(subsumption_resolution,[],[f41,f26])).
% 0.85/0.65  fof(f26,plain,(
% 0.85/0.65    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.85/0.65    inference(cnf_transformation,[],[f1])).
% 0.85/0.65  fof(f1,axiom,(
% 0.85/0.65    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.85/0.65  fof(f41,plain,(
% 0.85/0.65    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_tarski(sK1))),
% 0.85/0.65    inference(resolution,[],[f39,f38])).
% 0.85/0.65  fof(f38,plain,(
% 0.85/0.65    v1_subset_1(k1_tarski(sK1),sK0)),
% 0.85/0.65    inference(subsumption_resolution,[],[f37,f22])).
% 0.85/0.65  fof(f37,plain,(
% 0.85/0.65    v1_subset_1(k1_tarski(sK1),sK0) | v1_xboole_0(sK0)),
% 0.85/0.65    inference(subsumption_resolution,[],[f36,f23])).
% 0.85/0.65  fof(f36,plain,(
% 0.85/0.65    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.85/0.65    inference(superposition,[],[f24,f34])).
% 0.85/0.65  fof(f34,plain,(
% 0.85/0.65    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.85/0.65    inference(cnf_transformation,[],[f17])).
% 0.85/0.65  fof(f17,plain,(
% 0.85/0.65    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.85/0.65    inference(flattening,[],[f16])).
% 0.85/0.65  fof(f16,plain,(
% 0.85/0.65    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.85/0.65    inference(ennf_transformation,[],[f5])).
% 0.85/0.65  fof(f5,axiom,(
% 0.85/0.65    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.85/0.65  fof(f24,plain,(
% 0.85/0.65    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.85/0.65    inference(cnf_transformation,[],[f20])).
% 0.85/0.65  fof(f39,plain,(
% 0.85/0.65    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0)) )),
% 0.85/0.65    inference(resolution,[],[f35,f25])).
% 0.85/0.65  fof(f25,plain,(
% 0.85/0.65    v1_zfmisc_1(sK0)),
% 0.85/0.65    inference(cnf_transformation,[],[f20])).
% 0.85/0.65  fof(f35,plain,(
% 0.85/0.65    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.85/0.65    inference(subsumption_resolution,[],[f28,f27])).
% 0.85/0.65  fof(f27,plain,(
% 0.85/0.65    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.85/0.65    inference(cnf_transformation,[],[f11])).
% 0.85/0.65  fof(f11,plain,(
% 0.85/0.65    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.85/0.65    inference(ennf_transformation,[],[f4])).
% 0.85/0.65  fof(f4,axiom,(
% 0.85/0.65    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.85/0.65  fof(f28,plain,(
% 0.85/0.65    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.85/0.65    inference(cnf_transformation,[],[f13])).
% 0.85/0.65  fof(f13,plain,(
% 0.85/0.65    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.85/0.65    inference(flattening,[],[f12])).
% 0.85/0.65  fof(f12,plain,(
% 0.85/0.65    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.85/0.65    inference(ennf_transformation,[],[f6])).
% 0.85/0.65  fof(f6,axiom,(
% 0.85/0.65    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.85/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.85/0.65  % SZS output end Proof for theBenchmark
% 0.85/0.65  % (4149)------------------------------
% 0.85/0.65  % (4149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.65  % (4149)Termination reason: Refutation
% 0.85/0.65  
% 0.85/0.65  % (4149)Memory used [KB]: 6140
% 0.85/0.65  % (4149)Time elapsed: 0.056 s
% 0.85/0.65  % (4149)------------------------------
% 0.85/0.65  % (4149)------------------------------
% 0.85/0.65  % (3991)Success in time 0.288 s
%------------------------------------------------------------------------------
