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
% DateTime   : Thu Dec  3 13:20:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 104 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 385 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f28])).

fof(f28,plain,(
    ~ v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( ~ v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f110,plain,(
    v1_zfmisc_1(sK0) ),
    inference(subsumption_resolution,[],[f105,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f105,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_zfmisc_1(sK0) ),
    inference(superposition,[],[f89,f102])).

fof(f102,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f96,f54])).

fof(f54,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f27,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f96,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f60,f74])).

fof(f74,plain,(
    ~ v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f73,f27])).

fof(f73,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f30,plain,(
    ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X3] :
      ( v1_subset_1(k1_tarski(X3),X2)
      | k1_tarski(X3) = X2
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

% (3207)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_tarski(X0))
      | v1_zfmisc_1(k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k1_tarski(X2) != X1
      | v1_zfmisc_1(X1)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
     => ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_realset1)).

fof(f69,plain,(
    ! [X2,X1] :
      ( k1_tarski(X2) != X1
      | v1_zfmisc_1(X1)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( k1_tarski(X2) != X1
      | v1_zfmisc_1(X1)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f44,f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) != X0
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (3189)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.44  % (3189)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f110,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ~v1_zfmisc_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    (~v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X1] : (~v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (~v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & (~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    v1_zfmisc_1(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f105,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    m1_subset_1(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,sK0) | v1_zfmisc_1(sK0)),
% 0.21/0.44    inference(superposition,[],[f89,f102])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    sK0 = k1_tarski(sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f96,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    r2_hidden(sK1,sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f50,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ~v1_xboole_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f35,f29])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(nnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    sK0 = k1_tarski(sK1) | ~r2_hidden(sK1,sK0)),
% 0.21/0.44    inference(resolution,[],[f60,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ~v1_subset_1(k1_tarski(sK1),sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f73,f27])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ~v1_subset_1(k1_tarski(sK1),sK0) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f66,f29])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ~v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(superposition,[],[f30,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X2,X3] : (v1_subset_1(k1_tarski(X3),X2) | k1_tarski(X3) = X2 | ~r2_hidden(X3,X2)) )),
% 0.21/0.44    inference(resolution,[],[f41,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.44  % (3207)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(nnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(X0)) | v1_zfmisc_1(k1_tarski(X0))) )),
% 0.21/0.44    inference(equality_resolution,[],[f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k1_tarski(X2) != X1 | v1_zfmisc_1(X1) | ~m1_subset_1(X2,X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f69,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (~v1_zfmisc_1(X0) => ~v1_xboole_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_realset1)).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k1_tarski(X2) != X1 | v1_zfmisc_1(X1) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k1_tarski(X2) != X1 | v1_zfmisc_1(X1) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(superposition,[],[f44,f42])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_domain_1(X0,X1) != X0 | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f34,f31])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(rectify,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (3189)------------------------------
% 0.21/0.44  % (3189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (3189)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (3189)Memory used [KB]: 10618
% 0.21/0.44  % (3189)Time elapsed: 0.060 s
% 0.21/0.44  % (3189)------------------------------
% 0.21/0.44  % (3189)------------------------------
% 0.21/0.45  % (3186)Success in time 0.096 s
%------------------------------------------------------------------------------
