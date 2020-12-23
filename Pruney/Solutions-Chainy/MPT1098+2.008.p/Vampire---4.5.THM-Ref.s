%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  81 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 286 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f680,plain,(
    $false ),
    inference(subsumption_resolution,[],[f679,f66])).

fof(f66,plain,(
    v1_finset_1(sK4(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f56,f11])).

fof(f11,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(f56,plain,
    ( ~ v1_finset_1(sK0)
    | v1_finset_1(sK4(sK0,sK1,sK2)) ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | v1_finset_1(sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(f679,plain,(
    ~ v1_finset_1(sK4(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f670,f118])).

fof(f118,plain,(
    r1_tarski(sK4(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f102,f11])).

fof(f102,plain,
    ( ~ v1_finset_1(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f19,f12])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | r1_tarski(sK4(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f670,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),sK1)
    | ~ v1_finset_1(sK4(sK0,sK1,sK2)) ),
    inference(resolution,[],[f669,f10])).

fof(f10,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f669,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) ),
    inference(duplicate_literal_removal,[],[f667])).

fof(f667,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))
    | r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) ),
    inference(resolution,[],[f625,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f625,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,X1),k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f323,f174])).

fof(f174,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK5(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2)) ),
    inference(resolution,[],[f173,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f173,plain,(
    r1_tarski(sK5(sK0,sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f172,f11])).

fof(f172,plain,
    ( ~ v1_finset_1(sK0)
    | r1_tarski(sK5(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f21,f12])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | r1_tarski(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),X1)
      | r2_hidden(sK3(sK0,X0),X1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f301,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f301,plain,(
    ! [X87] :
      ( r2_hidden(sK3(sK0,X87),k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))
      | r1_tarski(sK0,X87) ) ),
    inference(resolution,[],[f35,f240])).

fof(f240,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f239,f11])).

fof(f239,plain,
    ( ~ v1_finset_1(sK0)
    | r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) ),
    inference(resolution,[],[f22,f12])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f13,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.41  % (11083)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.42  % (11083)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f680,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f679,f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    v1_finset_1(sK4(sK0,sK1,sK2))),
% 0.20/0.42    inference(subsumption_resolution,[],[f56,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    v1_finset_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ~v1_finset_1(sK0) | v1_finset_1(sK4(sK0,sK1,sK2))),
% 0.20/0.42    inference(resolution,[],[f18,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | v1_finset_1(sK4(X0,X1,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).
% 0.20/0.42  fof(f679,plain,(
% 0.20/0.42    ~v1_finset_1(sK4(sK0,sK1,sK2))),
% 0.20/0.42    inference(subsumption_resolution,[],[f670,f118])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    r1_tarski(sK4(sK0,sK1,sK2),sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f102,f11])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    ~v1_finset_1(sK0) | r1_tarski(sK4(sK0,sK1,sK2),sK1)),
% 0.20/0.42    inference(resolution,[],[f19,f12])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | r1_tarski(sK4(X0,X1,X2),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f670,plain,(
% 0.20/0.42    ~r1_tarski(sK4(sK0,sK1,sK2),sK1) | ~v1_finset_1(sK4(sK0,sK1,sK2))),
% 0.20/0.42    inference(resolution,[],[f669,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f669,plain,(
% 0.20/0.42    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f667])).
% 0.20/0.42  fof(f667,plain,(
% 0.20/0.42    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) | r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))),
% 0.20/0.42    inference(resolution,[],[f625,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.42  fof(f625,plain,(
% 0.20/0.42    ( ! [X1] : (r2_hidden(sK3(sK0,X1),k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) | r1_tarski(sK0,X1)) )),
% 0.20/0.42    inference(resolution,[],[f323,f174])).
% 0.20/0.42  fof(f174,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK5(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))) )),
% 0.20/0.42    inference(resolution,[],[f173,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.20/0.42  fof(f173,plain,(
% 0.20/0.42    r1_tarski(sK5(sK0,sK1,sK2),sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f172,f11])).
% 0.20/0.42  fof(f172,plain,(
% 0.20/0.42    ~v1_finset_1(sK0) | r1_tarski(sK5(sK0,sK1,sK2),sK2)),
% 0.20/0.42    inference(resolution,[],[f21,f12])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | r1_tarski(sK5(X0,X1,X2),X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f323,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),X1) | r2_hidden(sK3(sK0,X0),X1) | r1_tarski(sK0,X0)) )),
% 0.20/0.42    inference(resolution,[],[f301,f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f301,plain,(
% 0.20/0.42    ( ! [X87] : (r2_hidden(sK3(sK0,X87),k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) | r1_tarski(sK0,X87)) )),
% 0.20/0.42    inference(resolution,[],[f35,f240])).
% 0.20/0.42  fof(f240,plain,(
% 0.20/0.42    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))),
% 0.20/0.42    inference(subsumption_resolution,[],[f239,f11])).
% 0.20/0.42  fof(f239,plain,(
% 0.20/0.42    ~v1_finset_1(sK0) | r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))),
% 0.20/0.42    inference(resolution,[],[f22,f12])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(resolution,[],[f13,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (11083)------------------------------
% 0.20/0.42  % (11083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (11083)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (11083)Memory used [KB]: 5884
% 0.20/0.42  % (11083)Time elapsed: 0.015 s
% 0.20/0.42  % (11083)------------------------------
% 0.20/0.42  % (11083)------------------------------
% 0.20/0.43  % (11073)Success in time 0.08 s
%------------------------------------------------------------------------------
