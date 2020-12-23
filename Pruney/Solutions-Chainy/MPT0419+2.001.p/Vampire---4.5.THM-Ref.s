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
% DateTime   : Thu Dec  3 12:46:27 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   39 (  80 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 237 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(subsumption_resolution,[],[f272,f237])).

fof(f237,plain,(
    ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f236,f12])).

fof(f12,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f236,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f235,f37])).

fof(f37,plain,(
    ~ r2_hidden(sK3(sK1,sK2),sK2) ),
    inference(resolution,[],[f13,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f13,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f235,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f231,f14])).

% (6604)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f231,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(resolution,[],[f62,f86])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k3_subset_1(sK0,X2),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | r2_hidden(X2,sK2)
      | ~ r1_tarski(X3,k7_setfam_1(sK0,sK2)) ) ),
    inference(resolution,[],[f40,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X1] :
      ( ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
      | r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f11,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f11,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X1] :
      ( r2_hidden(k3_subset_1(X1,sK3(sK1,sK2)),k7_setfam_1(X1,sK1))
      | ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f36,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(resolution,[],[f13,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

% (6602)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f272,plain,(
    m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f254,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f254,plain,(
    r1_tarski(sK3(sK1,sK2),sK0) ),
    inference(resolution,[],[f134,f36])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f60,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f46,f17])).

fof(f46,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f14,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (721256449)
% 0.13/0.37  ipcrm: permission denied for id (721289218)
% 0.13/0.37  ipcrm: permission denied for id (722632707)
% 0.13/0.37  ipcrm: permission denied for id (726368260)
% 0.13/0.37  ipcrm: permission denied for id (721321989)
% 0.13/0.37  ipcrm: permission denied for id (721354758)
% 0.13/0.38  ipcrm: permission denied for id (721387527)
% 0.13/0.38  ipcrm: permission denied for id (728498184)
% 0.13/0.38  ipcrm: permission denied for id (721420297)
% 0.13/0.38  ipcrm: permission denied for id (728530954)
% 0.13/0.38  ipcrm: permission denied for id (728563723)
% 0.13/0.38  ipcrm: permission denied for id (722796556)
% 0.21/0.38  ipcrm: permission denied for id (728596493)
% 0.21/0.38  ipcrm: permission denied for id (726532110)
% 0.21/0.39  ipcrm: permission denied for id (722894863)
% 0.21/0.39  ipcrm: permission denied for id (726564880)
% 0.21/0.39  ipcrm: permission denied for id (722960401)
% 0.21/0.39  ipcrm: permission denied for id (726597650)
% 0.21/0.39  ipcrm: permission denied for id (723025939)
% 0.21/0.39  ipcrm: permission denied for id (723058708)
% 0.21/0.39  ipcrm: permission denied for id (723091477)
% 0.21/0.39  ipcrm: permission denied for id (726630422)
% 0.21/0.39  ipcrm: permission denied for id (723157015)
% 0.21/0.40  ipcrm: permission denied for id (723189784)
% 0.21/0.40  ipcrm: permission denied for id (723222553)
% 0.21/0.40  ipcrm: permission denied for id (726663194)
% 0.21/0.40  ipcrm: permission denied for id (726695963)
% 0.21/0.40  ipcrm: permission denied for id (726761501)
% 0.21/0.40  ipcrm: permission denied for id (723386398)
% 0.21/0.40  ipcrm: permission denied for id (721518623)
% 0.21/0.41  ipcrm: permission denied for id (721551392)
% 0.21/0.41  ipcrm: permission denied for id (721584161)
% 0.21/0.41  ipcrm: permission denied for id (726794274)
% 0.21/0.41  ipcrm: permission denied for id (721616931)
% 0.21/0.41  ipcrm: permission denied for id (723451940)
% 0.21/0.41  ipcrm: permission denied for id (726827045)
% 0.21/0.41  ipcrm: permission denied for id (721682470)
% 0.21/0.41  ipcrm: permission denied for id (723517479)
% 0.21/0.42  ipcrm: permission denied for id (729317416)
% 0.21/0.42  ipcrm: permission denied for id (729350185)
% 0.21/0.42  ipcrm: permission denied for id (729382954)
% 0.21/0.42  ipcrm: permission denied for id (723681323)
% 0.21/0.42  ipcrm: permission denied for id (723714092)
% 0.21/0.42  ipcrm: permission denied for id (723779629)
% 0.21/0.42  ipcrm: permission denied for id (727056430)
% 0.21/0.42  ipcrm: permission denied for id (728793135)
% 0.21/0.42  ipcrm: permission denied for id (728825904)
% 0.21/0.43  ipcrm: permission denied for id (727154737)
% 0.21/0.43  ipcrm: permission denied for id (727187506)
% 0.21/0.43  ipcrm: permission denied for id (727220275)
% 0.21/0.43  ipcrm: permission denied for id (724009012)
% 0.21/0.43  ipcrm: permission denied for id (724041781)
% 0.21/0.43  ipcrm: permission denied for id (721846326)
% 0.21/0.43  ipcrm: permission denied for id (724074551)
% 0.21/0.43  ipcrm: permission denied for id (727253048)
% 0.21/0.44  ipcrm: permission denied for id (727285817)
% 0.21/0.44  ipcrm: permission denied for id (724172858)
% 0.21/0.44  ipcrm: permission denied for id (724205627)
% 0.21/0.44  ipcrm: permission denied for id (724271165)
% 0.21/0.44  ipcrm: permission denied for id (729448510)
% 0.21/0.44  ipcrm: permission denied for id (727384127)
% 0.21/0.44  ipcrm: permission denied for id (727416896)
% 0.21/0.45  ipcrm: permission denied for id (728924225)
% 0.21/0.45  ipcrm: permission denied for id (727482434)
% 0.21/0.45  ipcrm: permission denied for id (724467779)
% 0.21/0.45  ipcrm: permission denied for id (727515204)
% 0.21/0.45  ipcrm: permission denied for id (724533317)
% 0.21/0.45  ipcrm: permission denied for id (727547974)
% 0.21/0.45  ipcrm: permission denied for id (724598855)
% 0.21/0.45  ipcrm: permission denied for id (727580744)
% 0.21/0.46  ipcrm: permission denied for id (724664393)
% 0.21/0.46  ipcrm: permission denied for id (724697162)
% 0.21/0.46  ipcrm: permission denied for id (724729931)
% 0.21/0.46  ipcrm: permission denied for id (727613516)
% 0.21/0.46  ipcrm: permission denied for id (724795469)
% 0.21/0.46  ipcrm: permission denied for id (724828238)
% 0.21/0.46  ipcrm: permission denied for id (727646287)
% 0.21/0.46  ipcrm: permission denied for id (724893776)
% 0.21/0.47  ipcrm: permission denied for id (727679057)
% 0.21/0.47  ipcrm: permission denied for id (727711826)
% 0.21/0.47  ipcrm: permission denied for id (724992083)
% 0.21/0.47  ipcrm: permission denied for id (727744596)
% 0.21/0.47  ipcrm: permission denied for id (727777365)
% 0.21/0.47  ipcrm: permission denied for id (725090390)
% 0.21/0.47  ipcrm: permission denied for id (727842904)
% 0.21/0.47  ipcrm: permission denied for id (725188697)
% 0.21/0.48  ipcrm: permission denied for id (727875674)
% 0.21/0.48  ipcrm: permission denied for id (728989787)
% 0.21/0.48  ipcrm: permission denied for id (725319773)
% 0.21/0.48  ipcrm: permission denied for id (729546846)
% 0.21/0.48  ipcrm: permission denied for id (725385311)
% 0.21/0.48  ipcrm: permission denied for id (729088096)
% 0.21/0.49  ipcrm: permission denied for id (725450849)
% 0.21/0.49  ipcrm: permission denied for id (722141282)
% 0.21/0.49  ipcrm: permission denied for id (722174051)
% 0.21/0.49  ipcrm: permission denied for id (728039524)
% 0.21/0.49  ipcrm: permission denied for id (722206821)
% 0.21/0.49  ipcrm: permission denied for id (725516390)
% 0.21/0.49  ipcrm: permission denied for id (725549159)
% 0.21/0.49  ipcrm: permission denied for id (725581928)
% 0.21/0.50  ipcrm: permission denied for id (728105066)
% 0.21/0.50  ipcrm: permission denied for id (722272363)
% 0.21/0.50  ipcrm: permission denied for id (729153644)
% 0.21/0.50  ipcrm: permission denied for id (728203374)
% 0.21/0.50  ipcrm: permission denied for id (722337903)
% 0.21/0.50  ipcrm: permission denied for id (725811312)
% 0.21/0.51  ipcrm: permission denied for id (722370673)
% 0.21/0.51  ipcrm: permission denied for id (728268914)
% 0.21/0.51  ipcrm: permission denied for id (725876851)
% 0.21/0.51  ipcrm: permission denied for id (725909620)
% 0.21/0.51  ipcrm: permission denied for id (725942389)
% 0.21/0.51  ipcrm: permission denied for id (726007926)
% 0.21/0.51  ipcrm: permission denied for id (722436215)
% 0.21/0.51  ipcrm: permission denied for id (726073464)
% 0.21/0.52  ipcrm: permission denied for id (726106233)
% 0.21/0.52  ipcrm: permission denied for id (728301690)
% 0.21/0.52  ipcrm: permission denied for id (729645179)
% 0.21/0.52  ipcrm: permission denied for id (728367228)
% 0.21/0.52  ipcrm: permission denied for id (728399997)
% 0.21/0.52  ipcrm: permission denied for id (726270078)
% 0.21/0.52  ipcrm: permission denied for id (728432767)
% 0.38/0.65  % (6594)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.38/0.65  % (6594)Refutation not found, incomplete strategy% (6594)------------------------------
% 0.38/0.65  % (6594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (6611)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.38/0.66  % (6601)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.38/0.66  % (6594)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (6594)Memory used [KB]: 10618
% 0.38/0.66  % (6594)Time elapsed: 0.084 s
% 0.38/0.66  % (6594)------------------------------
% 0.38/0.66  % (6594)------------------------------
% 0.38/0.66  % (6601)Refutation not found, incomplete strategy% (6601)------------------------------
% 0.38/0.66  % (6601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (6601)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (6601)Memory used [KB]: 10618
% 0.38/0.66  % (6601)Time elapsed: 0.098 s
% 0.38/0.66  % (6601)------------------------------
% 0.38/0.66  % (6601)------------------------------
% 0.38/0.68  % (6619)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.46/0.69  % (6603)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.46/0.69  % (6603)Refutation not found, incomplete strategy% (6603)------------------------------
% 0.46/0.69  % (6603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.69  % (6603)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.69  
% 0.46/0.69  % (6603)Memory used [KB]: 10618
% 0.46/0.69  % (6603)Time elapsed: 0.114 s
% 0.46/0.69  % (6603)------------------------------
% 0.46/0.69  % (6603)------------------------------
% 0.46/0.69  % (6614)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.46/0.69  % (6605)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.46/0.69  % (6592)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.46/0.69  % (6592)Refutation not found, incomplete strategy% (6592)------------------------------
% 0.46/0.69  % (6592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.69  % (6592)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.69  
% 0.46/0.69  % (6592)Memory used [KB]: 1663
% 0.46/0.69  % (6592)Time elapsed: 0.111 s
% 0.46/0.69  % (6592)------------------------------
% 0.46/0.69  % (6592)------------------------------
% 0.46/0.69  % (6597)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.46/0.70  % (6606)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.46/0.70  % (6615)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.46/0.70  % (6598)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.46/0.70  % (6593)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.46/0.70  % (6595)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.46/0.70  % (6599)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.46/0.70  % (6607)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.46/0.70  % (6605)Refutation found. Thanks to Tanya!
% 0.46/0.70  % SZS status Theorem for theBenchmark
% 0.46/0.70  % (6614)Refutation not found, incomplete strategy% (6614)------------------------------
% 0.46/0.70  % (6614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.70  % (6614)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.70  
% 0.46/0.70  % (6614)Memory used [KB]: 10618
% 0.46/0.70  % (6614)Time elapsed: 0.074 s
% 0.46/0.70  % (6614)------------------------------
% 0.46/0.70  % (6614)------------------------------
% 0.46/0.70  % (6596)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.46/0.71  % (6596)Refutation not found, incomplete strategy% (6596)------------------------------
% 0.46/0.71  % (6596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.71  % (6596)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.71  
% 0.46/0.71  % (6596)Memory used [KB]: 6140
% 0.46/0.71  % (6596)Time elapsed: 0.126 s
% 0.46/0.71  % (6596)------------------------------
% 0.46/0.71  % (6596)------------------------------
% 0.46/0.71  % (6621)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.46/0.71  % (6617)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.46/0.71  % (6610)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.46/0.71  % (6620)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.46/0.71  % (6613)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.46/0.71  % (6618)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.46/0.71  % (6609)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.46/0.72  % (6609)Refutation not found, incomplete strategy% (6609)------------------------------
% 0.46/0.72  % (6609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.72  % (6609)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.72  
% 0.46/0.72  % (6609)Memory used [KB]: 10618
% 0.46/0.72  % (6609)Time elapsed: 0.144 s
% 0.46/0.72  % (6609)------------------------------
% 0.46/0.72  % (6609)------------------------------
% 0.46/0.72  % (6612)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.46/0.72  % SZS output start Proof for theBenchmark
% 0.46/0.72  fof(f275,plain,(
% 0.46/0.72    $false),
% 0.46/0.72    inference(subsumption_resolution,[],[f272,f237])).
% 0.46/0.72  fof(f237,plain,(
% 0.46/0.72    ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.46/0.72    inference(subsumption_resolution,[],[f236,f12])).
% 0.46/0.72  fof(f12,plain,(
% 0.46/0.72    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.46/0.72    inference(cnf_transformation,[],[f8])).
% 0.46/0.72  fof(f8,plain,(
% 0.46/0.72    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.46/0.72    inference(flattening,[],[f7])).
% 0.46/0.72  fof(f7,plain,(
% 0.46/0.72    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.46/0.72    inference(ennf_transformation,[],[f6])).
% 0.46/0.72  fof(f6,negated_conjecture,(
% 0.46/0.72    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.46/0.72    inference(negated_conjecture,[],[f5])).
% 0.46/0.72  fof(f5,conjecture,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).
% 0.46/0.72  fof(f236,plain,(
% 0.46/0.72    ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.46/0.72    inference(subsumption_resolution,[],[f235,f37])).
% 0.46/0.72  fof(f37,plain,(
% 0.46/0.72    ~r2_hidden(sK3(sK1,sK2),sK2)),
% 0.46/0.72    inference(resolution,[],[f13,f19])).
% 0.46/0.72  fof(f19,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.46/0.72    inference(cnf_transformation,[],[f10])).
% 0.46/0.72  fof(f10,plain,(
% 0.46/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f1])).
% 0.46/0.72  fof(f1,axiom,(
% 0.46/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.46/0.72  fof(f13,plain,(
% 0.46/0.72    ~r1_tarski(sK1,sK2)),
% 0.46/0.72    inference(cnf_transformation,[],[f8])).
% 0.46/0.72  fof(f235,plain,(
% 0.46/0.72    ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK1,sK2),sK2) | ~r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.46/0.72    inference(subsumption_resolution,[],[f231,f14])).
% 0.46/0.72  % (6604)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.46/0.72  fof(f14,plain,(
% 0.46/0.72    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.46/0.72    inference(cnf_transformation,[],[f8])).
% 0.46/0.72  fof(f231,plain,(
% 0.46/0.72    ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(sK1,sK2),sK2) | ~r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.46/0.72    inference(duplicate_literal_removal,[],[f227])).
% 0.46/0.72  fof(f227,plain,(
% 0.46/0.72    ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK1,sK2),sK2) | ~r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.46/0.72    inference(resolution,[],[f62,f86])).
% 0.46/0.72  fof(f86,plain,(
% 0.46/0.72    ( ! [X2,X3] : (~r2_hidden(k3_subset_1(sK0,X2),X3) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r2_hidden(X2,sK2) | ~r1_tarski(X3,k7_setfam_1(sK0,sK2))) )),
% 0.46/0.72    inference(resolution,[],[f40,f17])).
% 0.46/0.72  fof(f17,plain,(
% 0.46/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.46/0.72    inference(cnf_transformation,[],[f10])).
% 0.46/0.72  fof(f40,plain,(
% 0.46/0.72    ( ! [X1] : (~r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2)) | r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.46/0.72    inference(resolution,[],[f11,f16])).
% 0.46/0.72  fof(f16,plain,(
% 0.46/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f9])).
% 0.46/0.72  fof(f9,plain,(
% 0.46/0.72    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.46/0.72    inference(ennf_transformation,[],[f4])).
% 0.46/0.72  fof(f4,axiom,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.46/0.72  fof(f11,plain,(
% 0.46/0.72    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.46/0.72    inference(cnf_transformation,[],[f8])).
% 0.46/0.72  fof(f62,plain,(
% 0.46/0.72    ( ! [X1] : (r2_hidden(k3_subset_1(X1,sK3(sK1,sK2)),k7_setfam_1(X1,sK1)) | ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 0.46/0.72    inference(resolution,[],[f36,f15])).
% 0.46/0.72  fof(f15,plain,(
% 0.46/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f9])).
% 0.46/0.72  fof(f36,plain,(
% 0.46/0.72    r2_hidden(sK3(sK1,sK2),sK1)),
% 0.46/0.72    inference(resolution,[],[f13,f18])).
% 0.46/0.72  fof(f18,plain,(
% 0.46/0.72    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.46/0.72    inference(cnf_transformation,[],[f10])).
% 0.46/0.72  % (6602)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.46/0.72  fof(f272,plain,(
% 0.46/0.72    m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.46/0.72    inference(resolution,[],[f254,f24])).
% 0.46/0.72  fof(f24,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f3])).
% 0.46/0.72  fof(f3,axiom,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.46/0.72  fof(f254,plain,(
% 0.46/0.72    r1_tarski(sK3(sK1,sK2),sK0)),
% 0.46/0.72    inference(resolution,[],[f134,f36])).
% 0.46/0.72  fof(f134,plain,(
% 0.46/0.72    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(X0,sK0)) )),
% 0.46/0.72    inference(resolution,[],[f60,f26])).
% 0.46/0.72  fof(f26,plain,(
% 0.46/0.72    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.46/0.72    inference(equality_resolution,[],[f21])).
% 0.46/0.72  fof(f21,plain,(
% 0.46/0.72    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.46/0.72    inference(cnf_transformation,[],[f2])).
% 0.46/0.72  fof(f2,axiom,(
% 0.46/0.72    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.46/0.72  fof(f60,plain,(
% 0.46/0.72    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.46/0.72    inference(resolution,[],[f46,f17])).
% 0.46/0.72  fof(f46,plain,(
% 0.46/0.72    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.46/0.72    inference(resolution,[],[f14,f25])).
% 0.46/0.72  fof(f25,plain,(
% 0.46/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f3])).
% 0.46/0.72  % SZS output end Proof for theBenchmark
% 0.46/0.72  % (6605)------------------------------
% 0.46/0.72  % (6605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.72  % (6605)Termination reason: Refutation
% 0.46/0.72  
% 0.46/0.72  % (6605)Memory used [KB]: 6268
% 0.46/0.72  % (6605)Time elapsed: 0.118 s
% 0.46/0.72  % (6605)------------------------------
% 0.46/0.72  % (6605)------------------------------
% 0.46/0.72  % (6602)Refutation not found, incomplete strategy% (6602)------------------------------
% 0.46/0.72  % (6602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.72  % (6602)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.72  
% 0.46/0.72  % (6602)Memory used [KB]: 10618
% 0.46/0.72  % (6602)Time elapsed: 0.145 s
% 0.46/0.72  % (6602)------------------------------
% 0.46/0.72  % (6602)------------------------------
% 0.46/0.73  % (6458)Success in time 0.36 s
%------------------------------------------------------------------------------
