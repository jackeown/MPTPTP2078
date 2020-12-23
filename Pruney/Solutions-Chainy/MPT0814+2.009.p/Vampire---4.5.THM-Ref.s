%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  76 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 245 expanded)
%              Number of equality atoms :   13 (  42 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f51,f63,f64,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,sK0),sK2)
      | ~ r2_hidden(sK6(X0,X1,sK0),sK1)
      | ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( sQ10_eqProxy(k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)),X3)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f27,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f31,plain,(
    ! [X4,X5] :
      ( ~ sQ10_eqProxy(k4_tarski(X4,X5),sK0)
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(equality_proxy_replacement,[],[f9,f30])).

fof(f9,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f64,plain,(
    r2_hidden(sK7(sK1,sK2,sK0),sK2) ),
    inference(resolution,[],[f51,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    r2_hidden(sK6(sK1,sK2,sK0),sK1) ),
    inference(resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f10,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f10,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X10] :
      ( ~ r1_tarski(sK3,X10)
      | r2_hidden(sK0,X10) ) ),
    inference(resolution,[],[f11,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f11,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (24192)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.49  % (24196)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (24192)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f51,f63,f64,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1,sK0),sK2) | ~r2_hidden(sK6(X0,X1,sK0),sK1) | ~r2_hidden(sK0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(resolution,[],[f31,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (sQ10_eqProxy(k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)),X3) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f27,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X1,X0] : (sQ10_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~sQ10_eqProxy(k4_tarski(X4,X5),sK0) | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f9,f30])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    r2_hidden(sK7(sK1,sK2,sK0),sK2)),
% 0.21/0.49    inference(resolution,[],[f51,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    r2_hidden(sK6(sK1,sK2,sK0),sK1)),
% 0.21/0.49    inference(resolution,[],[f51,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(resolution,[],[f44,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(resolution,[],[f10,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X10] : (~r1_tarski(sK3,X10) | r2_hidden(sK0,X10)) )),
% 0.21/0.49    inference(resolution,[],[f11,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (24192)------------------------------
% 0.21/0.49  % (24192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24192)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (24192)Memory used [KB]: 6268
% 0.21/0.49  % (24192)Time elapsed: 0.074 s
% 0.21/0.49  % (24192)------------------------------
% 0.21/0.49  % (24192)------------------------------
% 0.21/0.50  % (24178)Success in time 0.135 s
%------------------------------------------------------------------------------
