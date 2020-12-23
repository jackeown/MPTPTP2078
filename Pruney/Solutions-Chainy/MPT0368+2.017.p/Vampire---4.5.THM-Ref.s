%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:22 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 154 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 ( 535 expanded)
%              Number of equality atoms :   17 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f151])).

fof(f151,plain,(
    r2_hidden(sK4(sK1,sK0),sK1) ),
    inference(resolution,[],[f132,f72])).

fof(f72,plain,(
    ! [X1] :
      ( ~ r2_xboole_0(X1,sK0)
      | r2_hidden(sK4(X1,sK0),sK1) ) ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f31,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK0 != sK1
      & ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f132,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f131,f32])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,
    ( r2_xboole_0(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f118,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f118,plain,(
    r1_tarski(sK1,sK0) ),
    inference(forward_demodulation,[],[f115,f33])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f115,plain,(
    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f82,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f82,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f51,f47])).

fof(f51,plain,(
    r2_hidden(sK3(sK0),sK1) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f153,plain,(
    ~ r2_hidden(sK4(sK1,sK0),sK1) ),
    inference(resolution,[],[f132,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 16:14:57 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.44  % (11845)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.16/0.44  % (11832)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.16/0.44  % (11832)Refutation found. Thanks to Tanya!
% 0.16/0.44  % SZS status Theorem for theBenchmark
% 0.16/0.44  % SZS output start Proof for theBenchmark
% 0.16/0.44  fof(f155,plain,(
% 0.16/0.44    $false),
% 0.16/0.44    inference(subsumption_resolution,[],[f153,f151])).
% 0.16/0.44  fof(f151,plain,(
% 0.16/0.44    r2_hidden(sK4(sK1,sK0),sK1)),
% 0.16/0.44    inference(resolution,[],[f132,f72])).
% 0.16/0.44  fof(f72,plain,(
% 0.16/0.44    ( ! [X1] : (~r2_xboole_0(X1,sK0) | r2_hidden(sK4(X1,sK0),sK1)) )),
% 0.16/0.44    inference(resolution,[],[f54,f45])).
% 0.16/0.44  fof(f45,plain,(
% 0.16/0.44    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.16/0.44    inference(cnf_transformation,[],[f29])).
% 0.16/0.44  fof(f29,plain,(
% 0.16/0.44    ! [X0,X1] : ((~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.16/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f28])).
% 0.16/0.44  fof(f28,plain,(
% 0.16/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)))),
% 0.16/0.44    introduced(choice_axiom,[])).
% 0.16/0.44  fof(f15,plain,(
% 0.16/0.44    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.16/0.44    inference(ennf_transformation,[],[f3])).
% 0.16/0.44  fof(f3,axiom,(
% 0.16/0.44    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.16/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.16/0.44  fof(f54,plain,(
% 0.16/0.44    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) )),
% 0.16/0.44    inference(subsumption_resolution,[],[f52,f47])).
% 0.16/0.44  fof(f47,plain,(
% 0.16/0.44    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.16/0.44    inference(cnf_transformation,[],[f16])).
% 0.16/0.44  fof(f16,plain,(
% 0.16/0.44    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.16/0.44    inference(ennf_transformation,[],[f4])).
% 0.16/0.44  fof(f4,axiom,(
% 0.16/0.44    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.16/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.16/0.44  fof(f52,plain,(
% 0.16/0.44    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.16/0.44    inference(resolution,[],[f31,f38])).
% 0.16/0.44  fof(f38,plain,(
% 0.16/0.44    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.16/0.44    inference(cnf_transformation,[],[f25])).
% 0.16/0.44  fof(f25,plain,(
% 0.16/0.44    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.16/0.44    inference(nnf_transformation,[],[f13])).
% 0.16/0.44  fof(f13,plain,(
% 0.16/0.44    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.16/0.44    inference(ennf_transformation,[],[f7])).
% 0.16/0.44  fof(f7,axiom,(
% 0.16/0.44    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.16/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.16/0.44  fof(f31,plain,(
% 0.16/0.44    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.16/0.44    inference(cnf_transformation,[],[f18])).
% 0.16/0.44  fof(f18,plain,(
% 0.16/0.44    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.16/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.16/0.44  fof(f17,plain,(
% 0.16/0.44    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.16/0.44    introduced(choice_axiom,[])).
% 0.16/0.44  fof(f12,plain,(
% 0.16/0.44    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.16/0.44    inference(flattening,[],[f11])).
% 0.16/0.44  fof(f11,plain,(
% 0.16/0.44    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.16/0.44    inference(ennf_transformation,[],[f10])).
% 0.16/0.44  fof(f10,negated_conjecture,(
% 0.16/0.44    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.16/0.44    inference(negated_conjecture,[],[f9])).
% 0.16/0.44  fof(f9,conjecture,(
% 0.16/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.16/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.16/0.44  fof(f132,plain,(
% 0.16/0.44    r2_xboole_0(sK1,sK0)),
% 0.16/0.44    inference(subsumption_resolution,[],[f131,f32])).
% 0.16/0.44  fof(f32,plain,(
% 0.16/0.44    sK0 != sK1),
% 0.16/0.44    inference(cnf_transformation,[],[f18])).
% 0.16/0.44  fof(f131,plain,(
% 0.16/0.44    r2_xboole_0(sK1,sK0) | sK0 = sK1),
% 0.16/0.44    inference(resolution,[],[f118,f44])).
% 0.16/0.44  fof(f44,plain,(
% 0.16/0.44    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.16/0.44    inference(cnf_transformation,[],[f27])).
% 0.16/0.44  fof(f27,plain,(
% 0.16/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.16/0.44    inference(flattening,[],[f26])).
% 0.16/0.44  fof(f26,plain,(
% 0.16/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.16/0.44    inference(nnf_transformation,[],[f2])).
% 0.16/0.44  fof(f2,axiom,(
% 0.16/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.16/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.16/0.44  fof(f118,plain,(
% 0.16/0.44    r1_tarski(sK1,sK0)),
% 0.16/0.44    inference(forward_demodulation,[],[f115,f33])).
% 0.16/0.44  fof(f33,plain,(
% 0.16/0.44    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.16/0.44    inference(cnf_transformation,[],[f6])).
% 0.16/0.44  fof(f6,axiom,(
% 0.16/0.44    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.16/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.16/0.44  fof(f115,plain,(
% 0.16/0.44    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.16/0.44    inference(resolution,[],[f82,f41])).
% 0.16/0.45  fof(f41,plain,(
% 0.16/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f14])).
% 0.16/0.45  fof(f14,plain,(
% 0.16/0.45    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.16/0.45    inference(ennf_transformation,[],[f5])).
% 0.16/0.45  fof(f5,axiom,(
% 0.16/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.16/0.45  fof(f82,plain,(
% 0.16/0.45    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.16/0.45    inference(resolution,[],[f65,f49])).
% 0.16/0.45  fof(f49,plain,(
% 0.16/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.16/0.45    inference(resolution,[],[f30,f37])).
% 0.16/0.45  fof(f37,plain,(
% 0.16/0.45    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f25])).
% 0.16/0.45  fof(f30,plain,(
% 0.16/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.16/0.45    inference(cnf_transformation,[],[f18])).
% 0.16/0.45  fof(f65,plain,(
% 0.16/0.45    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.16/0.45    inference(resolution,[],[f55,f50])).
% 0.16/0.45  fof(f50,plain,(
% 0.16/0.45    v1_xboole_0(sK1) | ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.16/0.45    inference(resolution,[],[f30,f39])).
% 0.16/0.45  fof(f39,plain,(
% 0.16/0.45    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f25])).
% 0.16/0.45  fof(f55,plain,(
% 0.16/0.45    ~v1_xboole_0(sK1)),
% 0.16/0.45    inference(resolution,[],[f51,f47])).
% 0.16/0.45  fof(f51,plain,(
% 0.16/0.45    r2_hidden(sK3(sK0),sK1)),
% 0.16/0.45    inference(resolution,[],[f31,f36])).
% 0.16/0.45  fof(f36,plain,(
% 0.16/0.45    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f24])).
% 0.16/0.45  fof(f24,plain,(
% 0.16/0.45    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 0.16/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f23])).
% 0.16/0.45  fof(f23,plain,(
% 0.16/0.45    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 0.16/0.45    introduced(choice_axiom,[])).
% 0.16/0.45  fof(f8,axiom,(
% 0.16/0.45    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.16/0.45  fof(f153,plain,(
% 0.16/0.45    ~r2_hidden(sK4(sK1,sK0),sK1)),
% 0.16/0.45    inference(resolution,[],[f132,f46])).
% 0.16/0.45  fof(f46,plain,(
% 0.16/0.45    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f29])).
% 0.16/0.45  % SZS output end Proof for theBenchmark
% 0.16/0.45  % (11832)------------------------------
% 0.16/0.45  % (11832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.45  % (11832)Termination reason: Refutation
% 0.16/0.45  
% 0.16/0.45  % (11832)Memory used [KB]: 1663
% 0.16/0.45  % (11832)Time elapsed: 0.058 s
% 0.16/0.45  % (11832)------------------------------
% 0.16/0.45  % (11832)------------------------------
% 0.16/0.45  % (11822)Success in time 0.126 s
%------------------------------------------------------------------------------
