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
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  67 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 214 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(subsumption_resolution,[],[f111,f23])).

fof(f23,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    & r1_setfam_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
      & r1_setfam_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f111,plain,(
    r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    | r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(resolution,[],[f82,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f82,plain,(
    ! [X0] :
      ( r1_tarski(sK2(sK0,X0),k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X0) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( r1_tarski(sK2(sK0,X0),k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X0)
      | r1_tarski(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(sK2(sK0,X0),sK4(sK1,sK2(sK0,X0)))
      | r1_tarski(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(X0,sK4(sK1,X0)) ) ),
    inference(resolution,[],[f28,f22])).

fof(f22,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X4,X0)
      | r1_tarski(X4,sK4(X1,X4)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK3(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK4(X1,X4))
              & r2_hidden(sK4(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK4(X1,X4))
        & r2_hidden(sK4(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK4(sK1,sK2(sK0,X0)))
      | r1_tarski(X1,k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(sK4(sK1,sK2(sK0,X0)),k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f37,f25])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(sK4(sK1,X0),k3_tarski(sK1)) ) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK4(X1,X4),X1) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:10:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.40  % (7652)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.19/0.44  % (7660)WARNING: option uwaf not known.
% 0.19/0.44  % (7660)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.19/0.44  % (7660)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f112,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(subsumption_resolution,[],[f111,f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) & r1_setfam_1(sK0,sK1)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1)) => (~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) & r1_setfam_1(sK0,sK1))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f7,plain,(
% 0.19/0.44    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.44    inference(negated_conjecture,[],[f5])).
% 0.19/0.44  fof(f5,conjecture,(
% 0.19/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.19/0.44  fof(f111,plain,(
% 0.19/0.44    r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.19/0.44    inference(duplicate_literal_removal,[],[f109])).
% 0.19/0.44  fof(f109,plain,(
% 0.19/0.44    r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) | r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.19/0.44    inference(resolution,[],[f82,f26])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f9,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.19/0.44  fof(f82,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(sK2(sK0,X0),k3_tarski(sK1)) | r1_tarski(k3_tarski(sK0),X0)) )),
% 0.19/0.44    inference(duplicate_literal_removal,[],[f81])).
% 0.19/0.44  fof(f81,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(sK2(sK0,X0),k3_tarski(sK1)) | r1_tarski(k3_tarski(sK0),X0) | r1_tarski(k3_tarski(sK0),X0)) )),
% 0.19/0.44    inference(resolution,[],[f52,f38])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(sK2(sK0,X0),sK4(sK1,sK2(sK0,X0))) | r1_tarski(k3_tarski(sK0),X0)) )),
% 0.19/0.44    inference(resolution,[],[f35,f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f16])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK4(sK1,X0))) )),
% 0.19/0.44    inference(resolution,[],[f28,f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    r1_setfam_1(sK0,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ( ! [X4,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X4,X0) | r1_tarski(X4,sK4(X1,X4))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f20,f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.19/0.44    inference(rectify,[],[f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.19/0.44    inference(nnf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.19/0.44  fof(f52,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(X1,sK4(sK1,sK2(sK0,X0))) | r1_tarski(X1,k3_tarski(sK1)) | r1_tarski(k3_tarski(sK0),X0)) )),
% 0.19/0.44    inference(resolution,[],[f48,f31])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.44    inference(flattening,[],[f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(sK4(sK1,sK2(sK0,X0)),k3_tarski(sK1)) | r1_tarski(k3_tarski(sK0),X0)) )),
% 0.19/0.44    inference(resolution,[],[f37,f25])).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(sK4(sK1,X0),k3_tarski(sK1))) )),
% 0.19/0.44    inference(resolution,[],[f33,f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK1) | ~r2_hidden(X0,sK0)) )),
% 0.19/0.44    inference(resolution,[],[f27,f22])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ( ! [X4,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X4,X0) | r2_hidden(sK4(X1,X4),X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f21])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (7660)------------------------------
% 0.19/0.44  % (7660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (7660)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (7660)Memory used [KB]: 1023
% 0.19/0.44  % (7660)Time elapsed: 0.058 s
% 0.19/0.44  % (7660)------------------------------
% 0.19/0.44  % (7660)------------------------------
% 0.19/0.44  % (7647)Success in time 0.096 s
%------------------------------------------------------------------------------
