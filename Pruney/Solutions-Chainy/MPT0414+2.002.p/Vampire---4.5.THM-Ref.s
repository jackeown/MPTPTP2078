%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 102 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :   18
%              Number of atoms          :  126 ( 331 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f107])).

fof(f107,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f105,f18])).

fof(f18,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f105,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f103,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f103,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f92,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f92,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK2,X1),sK1)
      | r1_tarski(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X1] :
      ( r1_tarski(sK2,X1)
      | ~ r2_hidden(sK3(sK2,X1),sK2)
      | r2_hidden(sK3(sK2,X1),sK1) ) ),
    inference(resolution,[],[f77,f15])).

fof(f15,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0))
      | r1_tarski(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f75,f20])).

fof(f20,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f75,plain,(
    ! [X1] :
      ( r1_tarski(sK2,X1)
      | v1_xboole_0(k1_zfmisc_1(sK0))
      | m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f71,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_zfmisc_1(sK0))
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f69,f30])).

fof(f69,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | r2_hidden(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f52])).

fof(f52,plain,(
    r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f49,plain,(
    r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f46,f20])).

fof(f46,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f117,f31])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f114,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r2_hidden(sK3(sK1,X0),sK2)
      | ~ r2_hidden(sK3(sK1,X0),sK1) ) ),
    inference(resolution,[],[f85,f16])).

fof(f16,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK1,X1),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f83,f20])).

fof(f83,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | v1_xboole_0(k1_zfmisc_1(sK0))
      | m1_subset_1(sK3(sK1,X1),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f72,f23])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f70,f30])).

fof(f70,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f57])).

fof(f57,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f47,f20])).

fof(f47,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (25823)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (25822)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (25822)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f122,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f105,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    sK1 != sK2),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.54    inference(negated_conjecture,[],[f7])).
% 0.21/0.54  fof(f7,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK2) | sK1 = sK2),
% 0.21/0.54    inference(resolution,[],[f103,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    r1_tarski(sK2,sK1)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.21/0.54    inference(resolution,[],[f92,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK3(sK2,X1),sK1) | r1_tarski(sK2,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(sK2,X1) | ~r2_hidden(sK3(sK2,X1),sK2) | r2_hidden(sK3(sK2,X1),sK1)) )),
% 0.21/0.54    inference(resolution,[],[f77,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0)) | r1_tarski(sK2,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f75,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(sK2,X1) | v1_xboole_0(k1_zfmisc_1(sK0)) | m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f71,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_zfmisc_1(sK0)) | r1_tarski(sK2,X0)) )),
% 0.21/0.54    inference(resolution,[],[f69,f30])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2] : (~r2_hidden(X2,sK2) | r2_hidden(X2,k1_zfmisc_1(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f29,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f49,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f46,f20])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(resolution,[],[f24,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f117,f31])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK2) | r1_tarski(sK1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f30])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK3(sK1,X0),sK2) | ~r2_hidden(sK3(sK1,X0),sK1)) )),
% 0.21/0.54    inference(resolution,[],[f85,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(sK3(sK1,X1),k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f83,f20])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(sK1,X1) | v1_xboole_0(k1_zfmisc_1(sK0)) | m1_subset_1(sK3(sK1,X1),k1_zfmisc_1(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f72,f23])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(sK1,X0),k1_zfmisc_1(sK0)) | r1_tarski(sK1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f70,f30])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,k1_zfmisc_1(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f29,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f50,f38])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f47,f20])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(resolution,[],[f24,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (25822)------------------------------
% 0.21/0.54  % (25822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25822)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (25822)Memory used [KB]: 6268
% 0.21/0.54  % (25822)Time elapsed: 0.106 s
% 0.21/0.54  % (25822)------------------------------
% 0.21/0.54  % (25822)------------------------------
% 0.21/0.54  % (25815)Success in time 0.176 s
%------------------------------------------------------------------------------
