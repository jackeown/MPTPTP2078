%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:13 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  30 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  92 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f14,f24,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f24,plain,(
    r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f12,f13,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f13,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f5])).

% (8002)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:13:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.44  % (7995)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.45  % (7995)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f83,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f14,f24,f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,plain,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f12,f13,f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.45    inference(flattening,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.45    inference(nnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    r2_hidden(sK2,sK3)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f6,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 0.19/0.45    inference(flattening,[],[f5])).
% 0.19/0.45  % (8002)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.19/0.45  fof(f5,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.19/0.45    inference(negated_conjecture,[],[f3])).
% 0.19/0.45  fof(f3,conjecture,(
% 0.19/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    r2_hidden(sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (7995)------------------------------
% 0.19/0.45  % (7995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (7995)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (7995)Memory used [KB]: 895
% 0.19/0.45  % (7995)Time elapsed: 0.069 s
% 0.19/0.45  % (7995)------------------------------
% 0.19/0.45  % (7995)------------------------------
% 0.19/0.45  % (7987)Success in time 0.11 s
%------------------------------------------------------------------------------
