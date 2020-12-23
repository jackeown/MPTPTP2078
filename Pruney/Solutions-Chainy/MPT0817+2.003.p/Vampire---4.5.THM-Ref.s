%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:15 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   29 (  61 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 175 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f30,f29,f34,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f34,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f30,f19,f20,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f20,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(k1_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(k1_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f19,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

% (32225)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f22,f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f22,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:26:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.38  ipcrm: permission denied for id (803700737)
% 0.21/0.38  ipcrm: permission denied for id (807370754)
% 0.21/0.38  ipcrm: permission denied for id (802422787)
% 0.21/0.38  ipcrm: permission denied for id (810876932)
% 0.21/0.38  ipcrm: permission denied for id (809664517)
% 0.21/0.38  ipcrm: permission denied for id (803831814)
% 0.21/0.39  ipcrm: permission denied for id (803897352)
% 0.21/0.39  ipcrm: permission denied for id (807501833)
% 0.21/0.39  ipcrm: permission denied for id (802455562)
% 0.21/0.39  ipcrm: permission denied for id (803962891)
% 0.21/0.39  ipcrm: permission denied for id (803995660)
% 0.21/0.40  ipcrm: permission denied for id (807534605)
% 0.21/0.40  ipcrm: permission denied for id (804061198)
% 0.21/0.40  ipcrm: permission denied for id (809730063)
% 0.21/0.40  ipcrm: permission denied for id (804126736)
% 0.21/0.40  ipcrm: permission denied for id (810975250)
% 0.21/0.40  ipcrm: permission denied for id (809828371)
% 0.21/0.41  ipcrm: permission denied for id (802553876)
% 0.21/0.41  ipcrm: permission denied for id (807698453)
% 0.21/0.41  ipcrm: permission denied for id (807731222)
% 0.21/0.41  ipcrm: permission denied for id (804356119)
% 0.21/0.41  ipcrm: permission denied for id (807763992)
% 0.21/0.41  ipcrm: permission denied for id (809861145)
% 0.21/0.41  ipcrm: permission denied for id (804454426)
% 0.21/0.41  ipcrm: permission denied for id (807829531)
% 0.21/0.41  ipcrm: permission denied for id (802619420)
% 0.21/0.42  ipcrm: permission denied for id (802652189)
% 0.21/0.42  ipcrm: permission denied for id (804519966)
% 0.21/0.42  ipcrm: permission denied for id (809893919)
% 0.21/0.42  ipcrm: permission denied for id (807927841)
% 0.21/0.42  ipcrm: permission denied for id (804651042)
% 0.21/0.42  ipcrm: permission denied for id (807960611)
% 0.21/0.42  ipcrm: permission denied for id (807993380)
% 0.21/0.42  ipcrm: permission denied for id (808026149)
% 0.21/0.43  ipcrm: permission denied for id (808058918)
% 0.21/0.43  ipcrm: permission denied for id (804814887)
% 0.21/0.43  ipcrm: permission denied for id (802750504)
% 0.21/0.43  ipcrm: permission denied for id (811040809)
% 0.21/0.43  ipcrm: permission denied for id (808157226)
% 0.21/0.43  ipcrm: permission denied for id (804945964)
% 0.21/0.43  ipcrm: permission denied for id (808222765)
% 0.21/0.44  ipcrm: permission denied for id (810025006)
% 0.21/0.44  ipcrm: permission denied for id (802848815)
% 0.21/0.44  ipcrm: permission denied for id (805044272)
% 0.21/0.44  ipcrm: permission denied for id (805077041)
% 0.21/0.44  ipcrm: permission denied for id (810057778)
% 0.21/0.44  ipcrm: permission denied for id (802881587)
% 0.21/0.44  ipcrm: permission denied for id (805142580)
% 0.21/0.44  ipcrm: permission denied for id (805175349)
% 0.21/0.44  ipcrm: permission denied for id (805208118)
% 0.21/0.45  ipcrm: permission denied for id (811106359)
% 0.21/0.45  ipcrm: permission denied for id (805273656)
% 0.21/0.45  ipcrm: permission denied for id (805306425)
% 0.21/0.45  ipcrm: permission denied for id (805339194)
% 0.21/0.45  ipcrm: permission denied for id (805404732)
% 0.21/0.45  ipcrm: permission denied for id (802979901)
% 0.21/0.45  ipcrm: permission denied for id (811171902)
% 0.21/0.46  ipcrm: permission denied for id (805470271)
% 0.21/0.46  ipcrm: permission denied for id (803045440)
% 0.21/0.46  ipcrm: permission denied for id (810188865)
% 0.21/0.46  ipcrm: permission denied for id (811237443)
% 0.21/0.46  ipcrm: permission denied for id (803078213)
% 0.21/0.47  ipcrm: permission denied for id (808583239)
% 0.21/0.47  ipcrm: permission denied for id (811335752)
% 0.21/0.47  ipcrm: permission denied for id (808648777)
% 0.21/0.47  ipcrm: permission denied for id (808681546)
% 0.21/0.47  ipcrm: permission denied for id (808714315)
% 0.21/0.47  ipcrm: permission denied for id (803143756)
% 0.21/0.48  ipcrm: permission denied for id (805863502)
% 0.21/0.48  ipcrm: permission denied for id (805929040)
% 0.21/0.48  ipcrm: permission denied for id (808812625)
% 0.21/0.48  ipcrm: permission denied for id (808845394)
% 0.21/0.48  ipcrm: permission denied for id (806027347)
% 0.21/0.48  ipcrm: permission denied for id (808878164)
% 0.21/0.48  ipcrm: permission denied for id (806092885)
% 0.21/0.49  ipcrm: permission denied for id (806125654)
% 0.21/0.49  ipcrm: permission denied for id (806158423)
% 0.21/0.49  ipcrm: permission denied for id (806191192)
% 0.21/0.49  ipcrm: permission denied for id (811434073)
% 0.21/0.49  ipcrm: permission denied for id (808943706)
% 0.21/0.49  ipcrm: permission denied for id (806289499)
% 0.21/0.49  ipcrm: permission denied for id (803209309)
% 0.21/0.50  ipcrm: permission denied for id (806355038)
% 0.21/0.50  ipcrm: permission denied for id (806387807)
% 0.21/0.50  ipcrm: permission denied for id (809009248)
% 0.21/0.50  ipcrm: permission denied for id (809042017)
% 0.21/0.50  ipcrm: permission denied for id (803274850)
% 0.21/0.50  ipcrm: permission denied for id (806486115)
% 0.21/0.50  ipcrm: permission denied for id (809074788)
% 0.21/0.50  ipcrm: permission denied for id (810516581)
% 0.21/0.51  ipcrm: permission denied for id (803307622)
% 0.21/0.51  ipcrm: permission denied for id (806584423)
% 0.21/0.51  ipcrm: permission denied for id (803340392)
% 0.21/0.51  ipcrm: permission denied for id (810549353)
% 0.21/0.51  ipcrm: permission denied for id (806649962)
% 0.21/0.51  ipcrm: permission denied for id (810582123)
% 0.21/0.51  ipcrm: permission denied for id (806715500)
% 0.21/0.52  ipcrm: permission denied for id (806748269)
% 0.21/0.52  ipcrm: permission denied for id (806781038)
% 0.21/0.52  ipcrm: permission denied for id (810614895)
% 0.21/0.52  ipcrm: permission denied for id (806879344)
% 0.21/0.52  ipcrm: permission denied for id (803471473)
% 0.21/0.52  ipcrm: permission denied for id (809238642)
% 0.21/0.52  ipcrm: permission denied for id (810647667)
% 0.21/0.52  ipcrm: permission denied for id (803569780)
% 0.21/0.53  ipcrm: permission denied for id (810680437)
% 0.21/0.53  ipcrm: permission denied for id (807010422)
% 0.21/0.53  ipcrm: permission denied for id (811532408)
% 0.21/0.53  ipcrm: permission denied for id (810778745)
% 0.21/0.53  ipcrm: permission denied for id (809435258)
% 0.35/0.53  ipcrm: permission denied for id (810811515)
% 0.35/0.54  ipcrm: permission denied for id (809500796)
% 0.35/0.54  ipcrm: permission denied for id (807239805)
% 0.35/0.54  ipcrm: permission denied for id (809533566)
% 0.35/0.54  ipcrm: permission denied for id (809566335)
% 0.39/0.64  % (32216)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.39/0.65  % (32227)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.39/0.65  % (32216)Refutation found. Thanks to Tanya!
% 0.39/0.65  % SZS status Theorem for theBenchmark
% 0.39/0.65  % SZS output start Proof for theBenchmark
% 0.39/0.65  fof(f41,plain,(
% 0.39/0.65    $false),
% 0.39/0.65    inference(unit_resulting_resolution,[],[f30,f29,f34,f23])).
% 0.39/0.65  fof(f23,plain,(
% 0.39/0.65    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.39/0.65    inference(cnf_transformation,[],[f17])).
% 0.39/0.65  fof(f17,plain,(
% 0.39/0.65    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.39/0.65    inference(nnf_transformation,[],[f11])).
% 0.39/0.65  fof(f11,plain,(
% 0.39/0.65    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.39/0.65    inference(ennf_transformation,[],[f2])).
% 0.39/0.65  fof(f2,axiom,(
% 0.39/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.39/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.39/0.65  fof(f34,plain,(
% 0.39/0.65    ~r1_tarski(k2_relat_1(sK3),sK2)),
% 0.39/0.65    inference(unit_resulting_resolution,[],[f30,f19,f20,f25])).
% 0.39/0.65  fof(f25,plain,(
% 0.39/0.65    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.39/0.65    inference(cnf_transformation,[],[f13])).
% 0.39/0.65  fof(f13,plain,(
% 0.39/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.39/0.65    inference(flattening,[],[f12])).
% 0.39/0.65  fof(f12,plain,(
% 0.39/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.39/0.65    inference(ennf_transformation,[],[f5])).
% 0.39/0.65  fof(f5,axiom,(
% 0.39/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.39/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.39/0.65  fof(f20,plain,(
% 0.39/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.39/0.65    inference(cnf_transformation,[],[f16])).
% 0.39/0.65  fof(f16,plain,(
% 0.39/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.39/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).
% 0.39/0.65  fof(f15,plain,(
% 0.39/0.65    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.39/0.65    introduced(choice_axiom,[])).
% 0.39/0.65  fof(f9,plain,(
% 0.39/0.65    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.39/0.65    inference(flattening,[],[f8])).
% 0.39/0.65  fof(f8,plain,(
% 0.39/0.65    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.39/0.65    inference(ennf_transformation,[],[f7])).
% 0.39/0.65  fof(f7,negated_conjecture,(
% 0.39/0.65    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.39/0.65    inference(negated_conjecture,[],[f6])).
% 0.39/0.65  fof(f6,conjecture,(
% 0.39/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.39/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.39/0.65  fof(f19,plain,(
% 0.39/0.65    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.39/0.65    inference(cnf_transformation,[],[f16])).
% 0.39/0.65  fof(f29,plain,(
% 0.39/0.65    v5_relat_1(sK3,sK2)),
% 0.39/0.65    inference(unit_resulting_resolution,[],[f18,f27])).
% 0.39/0.65  fof(f27,plain,(
% 0.39/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.39/0.65    inference(cnf_transformation,[],[f14])).
% 0.39/0.65  % (32225)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.39/0.65  fof(f14,plain,(
% 0.39/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.39/0.65    inference(ennf_transformation,[],[f4])).
% 0.39/0.65  fof(f4,axiom,(
% 0.39/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.39/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.39/0.65  fof(f18,plain,(
% 0.39/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.39/0.65    inference(cnf_transformation,[],[f16])).
% 0.39/0.65  fof(f30,plain,(
% 0.39/0.65    v1_relat_1(sK3)),
% 0.39/0.65    inference(unit_resulting_resolution,[],[f22,f18,f21])).
% 0.39/0.65  fof(f21,plain,(
% 0.39/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.39/0.65    inference(cnf_transformation,[],[f10])).
% 0.39/0.65  fof(f10,plain,(
% 0.39/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.39/0.65    inference(ennf_transformation,[],[f1])).
% 0.39/0.65  fof(f1,axiom,(
% 0.39/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.39/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.39/0.65  fof(f22,plain,(
% 0.39/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.39/0.65    inference(cnf_transformation,[],[f3])).
% 0.39/0.65  fof(f3,axiom,(
% 0.39/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.39/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.39/0.65  % SZS output end Proof for theBenchmark
% 0.39/0.65  % (32216)------------------------------
% 0.39/0.65  % (32216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.65  % (32216)Termination reason: Refutation
% 0.39/0.65  
% 0.39/0.65  % (32216)Memory used [KB]: 895
% 0.39/0.65  % (32216)Time elapsed: 0.065 s
% 0.39/0.65  % (32216)------------------------------
% 0.39/0.65  % (32216)------------------------------
% 0.39/0.65  % (32062)Success in time 0.287 s
%------------------------------------------------------------------------------
