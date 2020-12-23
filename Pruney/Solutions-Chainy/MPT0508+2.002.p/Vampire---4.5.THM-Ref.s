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
% DateTime   : Thu Dec  3 12:48:39 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 117 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 ( 411 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f153,f423])).

fof(f423,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f383,f51,f41,f150])).

fof(f150,plain,
    ( spl4_16
  <=> r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f41,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f383,plain,
    ( r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f43,f53,f53,f60,f368,f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | ~ r1_tarski(k7_relat_1(X0,X1),X3)
      | r1_tarski(k7_relat_1(X0,X1),k7_relat_1(X3,X2))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f368,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f53,f70,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f70,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f53,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f53,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f43,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f153,plain,
    ( ~ spl4_16
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f140,f56,f51,f46,f36,f150])).

fof(f36,plain,
    ( spl4_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f56,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f140,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f38,f114,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f114,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f58,f53,f48,f29])).

fof(f48,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f58,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f38,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f59,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f36])).

fof(f27,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28292)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (28283)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (28281)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (28280)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (28279)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (28302)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (28284)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (28282)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (28291)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (28298)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (28294)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (28287)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (28301)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (28295)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  % (28290)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.34/0.53  % (28285)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.34/0.53  % (28286)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.53  % (28296)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.34/0.54  % (28289)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.34/0.54  % (28285)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (28299)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.34/0.54  % (28297)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.34/0.54  % (28300)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.34/0.54  % (28288)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.34/0.54  % (28299)Refutation not found, incomplete strategy% (28299)------------------------------
% 1.34/0.54  % (28299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28293)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.34/0.54  % (28299)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (28299)Memory used [KB]: 6140
% 1.34/0.54  % (28299)Time elapsed: 0.094 s
% 1.34/0.54  % (28299)------------------------------
% 1.34/0.54  % (28299)------------------------------
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f424,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f153,f423])).
% 1.46/0.55  fof(f423,plain,(
% 1.46/0.55    spl4_16 | ~spl4_2 | ~spl4_4),
% 1.46/0.55    inference(avatar_split_clause,[],[f383,f51,f41,f150])).
% 1.46/0.55  fof(f150,plain,(
% 1.46/0.55    spl4_16 <=> r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.46/0.55  fof(f41,plain,(
% 1.46/0.55    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.46/0.55  fof(f51,plain,(
% 1.46/0.55    spl4_4 <=> v1_relat_1(sK3)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.46/0.55  fof(f383,plain,(
% 1.46/0.55    r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1)) | (~spl4_2 | ~spl4_4)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f43,f53,f53,f60,f368,f115])).
% 1.46/0.55  fof(f115,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | ~r1_tarski(k7_relat_1(X0,X1),X3) | r1_tarski(k7_relat_1(X0,X1),k7_relat_1(X3,X2)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 1.46/0.55    inference(superposition,[],[f29,f28])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f12])).
% 1.46/0.55  fof(f12,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(flattening,[],[f11])).
% 1.46/0.55  fof(f11,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(ennf_transformation,[],[f4])).
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f14])).
% 1.46/0.55  fof(f14,plain,(
% 1.46/0.55    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.46/0.55    inference(flattening,[],[f13])).
% 1.46/0.55  fof(f13,plain,(
% 1.46/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f5])).
% 1.46/0.55  fof(f5,axiom,(
% 1.46/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 1.46/0.55  fof(f368,plain,(
% 1.46/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_4),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f53,f70,f34])).
% 1.46/0.55  fof(f34,plain,(
% 1.46/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f18])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.55    inference(ennf_transformation,[],[f3])).
% 1.46/0.55  fof(f3,axiom,(
% 1.46/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.46/0.55  fof(f70,plain,(
% 1.46/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))) ) | ~spl4_4),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f60,f33])).
% 1.46/0.55  fof(f33,plain,(
% 1.46/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.46/0.55    inference(nnf_transformation,[],[f2])).
% 1.46/0.55  fof(f2,axiom,(
% 1.46/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) ) | ~spl4_4),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f53,f30])).
% 1.46/0.55  fof(f30,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f15])).
% 1.46/0.55  fof(f15,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f6])).
% 1.46/0.55  fof(f6,axiom,(
% 1.46/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.46/0.55  fof(f53,plain,(
% 1.46/0.55    v1_relat_1(sK3) | ~spl4_4),
% 1.46/0.55    inference(avatar_component_clause,[],[f51])).
% 1.46/0.55  fof(f43,plain,(
% 1.46/0.55    r1_tarski(sK0,sK1) | ~spl4_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f41])).
% 1.46/0.55  fof(f153,plain,(
% 1.46/0.55    ~spl4_16 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 1.46/0.55    inference(avatar_split_clause,[],[f140,f56,f51,f46,f36,f150])).
% 1.46/0.55  fof(f36,plain,(
% 1.46/0.55    spl4_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.46/0.55  fof(f46,plain,(
% 1.46/0.55    spl4_3 <=> r1_tarski(sK2,sK3)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.46/0.55  fof(f56,plain,(
% 1.46/0.55    spl4_5 <=> v1_relat_1(sK2)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.46/0.55  fof(f140,plain,(
% 1.46/0.55    ~r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f38,f114,f31])).
% 1.46/0.55  fof(f31,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f17])).
% 1.46/0.55  fof(f17,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.46/0.55    inference(flattening,[],[f16])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.46/0.55    inference(ennf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.46/0.55  fof(f114,plain,(
% 1.46/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f58,f53,f48,f29])).
% 1.46/0.55  fof(f48,plain,(
% 1.46/0.55    r1_tarski(sK2,sK3) | ~spl4_3),
% 1.46/0.55    inference(avatar_component_clause,[],[f46])).
% 1.46/0.55  fof(f58,plain,(
% 1.46/0.55    v1_relat_1(sK2) | ~spl4_5),
% 1.46/0.55    inference(avatar_component_clause,[],[f56])).
% 1.46/0.55  fof(f38,plain,(
% 1.46/0.55    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | spl4_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f36])).
% 1.46/0.55  fof(f59,plain,(
% 1.46/0.55    spl4_5),
% 1.46/0.55    inference(avatar_split_clause,[],[f23,f56])).
% 1.46/0.55  fof(f23,plain,(
% 1.46/0.55    v1_relat_1(sK2)),
% 1.46/0.55    inference(cnf_transformation,[],[f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19])).
% 1.46/0.55  fof(f19,plain,(
% 1.46/0.55    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f20,plain,(
% 1.46/0.55    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f10,plain,(
% 1.46/0.55    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.46/0.55    inference(flattening,[],[f9])).
% 1.46/0.55  fof(f9,plain,(
% 1.46/0.55    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.46/0.55    inference(ennf_transformation,[],[f8])).
% 1.46/0.55  fof(f8,negated_conjecture,(
% 1.46/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 1.46/0.55    inference(negated_conjecture,[],[f7])).
% 1.46/0.55  fof(f7,conjecture,(
% 1.46/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 1.46/0.55  fof(f54,plain,(
% 1.46/0.55    spl4_4),
% 1.46/0.55    inference(avatar_split_clause,[],[f24,f51])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    v1_relat_1(sK3)),
% 1.46/0.55    inference(cnf_transformation,[],[f21])).
% 1.46/0.55  fof(f49,plain,(
% 1.46/0.55    spl4_3),
% 1.46/0.55    inference(avatar_split_clause,[],[f25,f46])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    r1_tarski(sK2,sK3)),
% 1.46/0.55    inference(cnf_transformation,[],[f21])).
% 1.46/0.55  fof(f44,plain,(
% 1.46/0.55    spl4_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f26,f41])).
% 1.46/0.55  fof(f26,plain,(
% 1.46/0.55    r1_tarski(sK0,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f21])).
% 1.46/0.55  fof(f39,plain,(
% 1.46/0.55    ~spl4_1),
% 1.46/0.55    inference(avatar_split_clause,[],[f27,f36])).
% 1.46/0.55  fof(f27,plain,(
% 1.46/0.55    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 1.46/0.55    inference(cnf_transformation,[],[f21])).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (28285)------------------------------
% 1.46/0.55  % (28285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (28285)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (28285)Memory used [KB]: 11001
% 1.46/0.55  % (28285)Time elapsed: 0.112 s
% 1.46/0.55  % (28285)------------------------------
% 1.46/0.55  % (28285)------------------------------
% 1.46/0.56  % (28278)Success in time 0.191 s
%------------------------------------------------------------------------------
