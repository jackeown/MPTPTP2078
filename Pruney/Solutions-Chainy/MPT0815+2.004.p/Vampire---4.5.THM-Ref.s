%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:12 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   28 (  42 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 114 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f26,plain,(
    ~ m1_subset_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f17,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

fof(f36,plain,(
    r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f33,f16])).

fof(f16,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK0,X0),k2_zfmisc_1(sK1,X1)) ) ),
    inference(resolution,[],[f25,f15])).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (821264387)
% 0.13/0.37  ipcrm: permission denied for id (825196548)
% 0.13/0.37  ipcrm: permission denied for id (825229317)
% 0.13/0.37  ipcrm: permission denied for id (821329926)
% 0.13/0.37  ipcrm: permission denied for id (821395464)
% 0.13/0.37  ipcrm: permission denied for id (821461001)
% 0.13/0.38  ipcrm: permission denied for id (821493770)
% 0.13/0.38  ipcrm: permission denied for id (825327628)
% 0.13/0.38  ipcrm: permission denied for id (821559309)
% 0.13/0.38  ipcrm: permission denied for id (821592078)
% 0.13/0.38  ipcrm: permission denied for id (821624847)
% 0.13/0.38  ipcrm: permission denied for id (821657616)
% 0.13/0.38  ipcrm: permission denied for id (821690385)
% 0.13/0.39  ipcrm: permission denied for id (821723154)
% 0.21/0.39  ipcrm: permission denied for id (821755924)
% 0.21/0.39  ipcrm: permission denied for id (821788693)
% 0.21/0.39  ipcrm: permission denied for id (825425943)
% 0.21/0.39  ipcrm: permission denied for id (825458712)
% 0.21/0.40  ipcrm: permission denied for id (821985308)
% 0.21/0.40  ipcrm: permission denied for id (822050847)
% 0.21/0.40  ipcrm: permission denied for id (822083616)
% 0.21/0.40  ipcrm: permission denied for id (825655329)
% 0.21/0.41  ipcrm: permission denied for id (825688098)
% 0.21/0.41  ipcrm: permission denied for id (822181924)
% 0.21/0.41  ipcrm: permission denied for id (822214693)
% 0.21/0.41  ipcrm: permission denied for id (822280231)
% 0.21/0.42  ipcrm: permission denied for id (822345769)
% 0.21/0.42  ipcrm: permission denied for id (822411307)
% 0.21/0.42  ipcrm: permission denied for id (822476845)
% 0.21/0.42  ipcrm: permission denied for id (825884718)
% 0.21/0.42  ipcrm: permission denied for id (825917487)
% 0.21/0.42  ipcrm: permission denied for id (822575152)
% 0.21/0.43  ipcrm: permission denied for id (822673458)
% 0.21/0.43  ipcrm: permission denied for id (825983027)
% 0.21/0.43  ipcrm: permission denied for id (822771765)
% 0.21/0.43  ipcrm: permission denied for id (822804534)
% 0.21/0.43  ipcrm: permission denied for id (822870072)
% 0.21/0.44  ipcrm: permission denied for id (826179643)
% 0.21/0.44  ipcrm: permission denied for id (826212412)
% 0.21/0.44  ipcrm: permission denied for id (822968381)
% 0.21/0.44  ipcrm: permission denied for id (826245182)
% 0.21/0.44  ipcrm: permission denied for id (823033919)
% 0.21/0.44  ipcrm: permission denied for id (826277952)
% 0.21/0.45  ipcrm: permission denied for id (823099458)
% 0.21/0.45  ipcrm: permission denied for id (823132227)
% 0.21/0.45  ipcrm: permission denied for id (823164996)
% 0.21/0.45  ipcrm: permission denied for id (826343493)
% 0.21/0.45  ipcrm: permission denied for id (823230534)
% 0.21/0.45  ipcrm: permission denied for id (823263303)
% 0.21/0.46  ipcrm: permission denied for id (826409033)
% 0.21/0.46  ipcrm: permission denied for id (823394379)
% 0.21/0.46  ipcrm: permission denied for id (826507341)
% 0.21/0.46  ipcrm: permission denied for id (826572879)
% 0.21/0.47  ipcrm: permission denied for id (826605648)
% 0.21/0.47  ipcrm: permission denied for id (823623761)
% 0.21/0.47  ipcrm: permission denied for id (823656530)
% 0.21/0.47  ipcrm: permission denied for id (823689299)
% 0.21/0.47  ipcrm: permission denied for id (823722068)
% 0.21/0.47  ipcrm: permission denied for id (823754837)
% 0.21/0.47  ipcrm: permission denied for id (826638422)
% 0.21/0.47  ipcrm: permission denied for id (823820375)
% 0.21/0.48  ipcrm: permission denied for id (823853145)
% 0.21/0.48  ipcrm: permission denied for id (823885914)
% 0.21/0.48  ipcrm: permission denied for id (823918683)
% 0.21/0.48  ipcrm: permission denied for id (823951452)
% 0.21/0.48  ipcrm: permission denied for id (823984221)
% 0.21/0.49  ipcrm: permission denied for id (824082528)
% 0.21/0.49  ipcrm: permission denied for id (824115297)
% 0.21/0.49  ipcrm: permission denied for id (824148066)
% 0.21/0.49  ipcrm: permission denied for id (826769507)
% 0.21/0.49  ipcrm: permission denied for id (824213604)
% 0.21/0.49  ipcrm: permission denied for id (824279142)
% 0.21/0.50  ipcrm: permission denied for id (824311911)
% 0.21/0.50  ipcrm: permission denied for id (826867817)
% 0.21/0.50  ipcrm: permission denied for id (824410218)
% 0.21/0.50  ipcrm: permission denied for id (824442987)
% 0.21/0.50  ipcrm: permission denied for id (826900588)
% 0.21/0.51  ipcrm: permission denied for id (824541295)
% 0.21/0.51  ipcrm: permission denied for id (827031665)
% 0.21/0.51  ipcrm: permission denied for id (824639602)
% 0.21/0.51  ipcrm: permission denied for id (824737908)
% 0.21/0.51  ipcrm: permission denied for id (827097205)
% 0.21/0.51  ipcrm: permission denied for id (827129974)
% 0.21/0.52  ipcrm: permission denied for id (824868985)
% 0.21/0.52  ipcrm: permission denied for id (824901754)
% 0.21/0.52  ipcrm: permission denied for id (824934523)
% 0.36/0.52  ipcrm: permission denied for id (824967292)
% 0.36/0.52  ipcrm: permission denied for id (827228285)
% 0.36/0.53  ipcrm: permission denied for id (825065599)
% 0.39/0.61  % (3550)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.39/0.61  % (3550)Refutation found. Thanks to Tanya!
% 0.39/0.61  % SZS status Theorem for theBenchmark
% 0.39/0.61  % SZS output start Proof for theBenchmark
% 0.39/0.62  fof(f44,plain,(
% 0.39/0.62    $false),
% 0.39/0.62    inference(resolution,[],[f36,f32])).
% 0.39/0.62  fof(f32,plain,(
% 0.39/0.62    ~r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.39/0.62    inference(resolution,[],[f26,f29])).
% 0.39/0.62  fof(f29,plain,(
% 0.39/0.62    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.39/0.62    inference(resolution,[],[f27,f22])).
% 0.39/0.62  fof(f22,plain,(
% 0.39/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.39/0.62    inference(cnf_transformation,[],[f12])).
% 0.39/0.62  fof(f12,plain,(
% 0.39/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.39/0.62    inference(nnf_transformation,[],[f4])).
% 0.39/0.62  fof(f4,axiom,(
% 0.39/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.39/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.39/0.62  fof(f27,plain,(
% 0.39/0.62    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f20,f18])).
% 0.39/0.62  fof(f18,plain,(
% 0.39/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f1])).
% 0.39/0.62  fof(f1,axiom,(
% 0.39/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.39/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.39/0.62  fof(f20,plain,(
% 0.39/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f11])).
% 0.39/0.62  fof(f11,plain,(
% 0.39/0.62    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.39/0.62    inference(nnf_transformation,[],[f2])).
% 0.39/0.62  fof(f2,axiom,(
% 0.39/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.39/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.39/0.62  fof(f26,plain,(
% 0.39/0.62    ~m1_subset_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.39/0.62    inference(definition_unfolding,[],[f17,f18])).
% 0.39/0.62  fof(f17,plain,(
% 0.39/0.62    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.39/0.62    inference(cnf_transformation,[],[f10])).
% 0.39/0.62  fof(f10,plain,(
% 0.39/0.62    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1)),
% 0.39/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.39/0.62  fof(f9,plain,(
% 0.39/0.62    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1))),
% 0.39/0.62    introduced(choice_axiom,[])).
% 0.39/0.62  fof(f8,plain,(
% 0.39/0.62    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 0.39/0.62    inference(flattening,[],[f7])).
% 0.39/0.62  fof(f7,plain,(
% 0.39/0.62    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 0.39/0.62    inference(ennf_transformation,[],[f6])).
% 0.39/0.62  fof(f6,negated_conjecture,(
% 0.39/0.62    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.39/0.62    inference(negated_conjecture,[],[f5])).
% 0.39/0.62  fof(f5,conjecture,(
% 0.39/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.39/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).
% 0.39/0.62  fof(f36,plain,(
% 0.39/0.62    r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.39/0.62    inference(resolution,[],[f33,f16])).
% 0.39/0.62  fof(f16,plain,(
% 0.39/0.62    r2_hidden(sK2,sK3)),
% 0.39/0.62    inference(cnf_transformation,[],[f10])).
% 0.39/0.62  fof(f33,plain,(
% 0.39/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK0,X0),k2_zfmisc_1(sK1,X1))) )),
% 0.39/0.62    inference(resolution,[],[f25,f15])).
% 0.39/0.62  fof(f15,plain,(
% 0.39/0.62    r2_hidden(sK0,sK1)),
% 0.39/0.62    inference(cnf_transformation,[],[f10])).
% 0.39/0.62  fof(f25,plain,(
% 0.39/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.39/0.62    inference(cnf_transformation,[],[f14])).
% 0.39/0.62  fof(f14,plain,(
% 0.39/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.39/0.62    inference(flattening,[],[f13])).
% 0.39/0.62  fof(f13,plain,(
% 0.39/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.39/0.62    inference(nnf_transformation,[],[f3])).
% 0.39/0.62  fof(f3,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.39/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.39/0.62  % SZS output end Proof for theBenchmark
% 0.39/0.62  % (3550)------------------------------
% 0.39/0.62  % (3550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.62  % (3550)Termination reason: Refutation
% 0.39/0.62  
% 0.39/0.62  % (3550)Memory used [KB]: 1535
% 0.39/0.62  % (3550)Time elapsed: 0.030 s
% 0.39/0.62  % (3550)------------------------------
% 0.39/0.62  % (3550)------------------------------
% 0.39/0.62  % (3327)Success in time 0.261 s
%------------------------------------------------------------------------------
