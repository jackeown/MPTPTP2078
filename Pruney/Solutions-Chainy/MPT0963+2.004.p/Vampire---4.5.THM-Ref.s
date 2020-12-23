%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 327 expanded)
%              Number of leaves         :    5 (  56 expanded)
%              Depth                    :   23
%              Number of atoms          :  185 (1832 expanded)
%              Number of equality atoms :   28 ( 264 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f128])).

fof(f128,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f121,f65])).

fof(f65,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK2),X4)
      | v1_funct_2(sK2,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f64,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f64,plain,(
    ! [X4] :
      ( v1_funct_2(sK2,sK0,X4)
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X4) ) ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X4] :
      ( v1_funct_2(sK2,sK0,X4)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X4) ) ),
    inference(superposition,[],[f29,f20])).

fof(f20,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f121,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f120,f45])).

fof(f45,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f35,f20])).

fof(f35,plain,(
    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f120,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f119,f19])).

fof(f119,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f18])).

fof(f115,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f28,f107])).

fof(f107,plain,(
    sK0 = k10_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f106,f89])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0,sK0),sK0)
      | sK0 = k10_relat_1(sK2,X0) ) ),
    inference(factoring,[],[f63])).

fof(f63,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(sK2,X2,X3),sK0)
      | r2_hidden(sK3(sK2,X2,X3),X3)
      | k10_relat_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f62,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(sK2,X2,X3),sK0)
      | ~ v1_funct_1(sK2)
      | r2_hidden(sK3(sK2,X2,X3),X3)
      | k10_relat_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f57,f18])).

fof(f57,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(sK2,X2,X3),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(sK3(sK2,X2,X3),X3)
      | k10_relat_1(sK2,X2) = X3 ) ),
    inference(superposition,[],[f23,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f106,plain,
    ( ~ r2_hidden(sK3(sK2,sK1,sK0),sK0)
    | sK0 = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f105,f20])).

fof(f105,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f104,f89])).

fof(f104,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK2,sK1,sK0),sK0) ),
    inference(subsumption_resolution,[],[f103,f19])).

fof(f103,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK2,sK1,sK0),sK0) ),
    inference(subsumption_resolution,[],[f98,f18])).

fof(f98,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK2,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK2,sK1,sK0),sK0)
    | sK0 = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f95,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,sK3(sK2,X1,sK0)),sK1)
      | sK0 = k10_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f89,f16])).

fof(f16,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(k1_funct_1(sK2,X3),sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f129,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f127,f34])).

fof(f34,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f17,f19])).

fof(f17,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f127,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f121,f67])).

fof(f67,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_relat_1(sK2),X5)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) ) ),
    inference(subsumption_resolution,[],[f66,f19])).

fof(f66,plain,(
    ! [X5] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X5) ) ),
    inference(subsumption_resolution,[],[f59,f18])).

fof(f59,plain,(
    ! [X5] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X5) ) ),
    inference(superposition,[],[f30,f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (26486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (26501)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (26495)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (26487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (26494)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (26490)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (26494)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f121,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X4] : (~r1_tarski(k2_relat_1(sK2),X4) | v1_funct_2(sK2,sK0,X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X4] : (v1_funct_2(sK2,sK0,X4) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f58,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X4] : (v1_funct_2(sK2,sK0,X4) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X4)) )),
% 0.21/0.49    inference(superposition,[],[f29,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f120,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.21/0.49    inference(forward_demodulation,[],[f35,f20])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f18,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f19])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK0),sK1) | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f115,f18])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK0),sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(superposition,[],[f28,f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(sK2,X0,sK0),sK0) | sK0 = k10_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(factoring,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(sK3(sK2,X2,X3),sK0) | r2_hidden(sK3(sK2,X2,X3),X3) | k10_relat_1(sK2,X2) = X3) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f62,f19])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(sK3(sK2,X2,X3),sK0) | ~v1_funct_1(sK2) | r2_hidden(sK3(sK2,X2,X3),X3) | k10_relat_1(sK2,X2) = X3) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f57,f18])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(sK3(sK2,X2,X3),sK0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK3(sK2,X2,X3),X3) | k10_relat_1(sK2,X2) = X3) )),
% 0.21/0.49    inference(superposition,[],[f23,f20])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK3(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK2,sK1,sK0),sK0) | sK0 = k10_relat_1(sK2,sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f105,f20])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f104,f89])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK3(sK2,sK1,sK0),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f19])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK3(sK2,sK1,sK0),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f18])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK3(sK2,sK1,sK0),sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(sK2,sK1,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK3(sK2,sK1,sK0),sK0) | sK0 = k10_relat_1(sK2,sK1)),
% 0.21/0.49    inference(resolution,[],[f95,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,sK3(sK2,X1,sK0)),sK1) | sK0 = k10_relat_1(sK2,X1)) )),
% 0.21/0.49    inference(resolution,[],[f89,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(k1_funct_1(sK2,X3),sK1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f127,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f17,f19])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(resolution,[],[f121,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X5] : (~r1_tarski(k2_relat_1(sK2),X5) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f66,f19])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X5] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X5)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f18])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X5] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X5)) )),
% 0.21/0.49    inference(superposition,[],[f30,f20])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (26494)------------------------------
% 0.21/0.49  % (26494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26494)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (26494)Memory used [KB]: 1663
% 0.21/0.49  % (26494)Time elapsed: 0.068 s
% 0.21/0.49  % (26494)------------------------------
% 0.21/0.49  % (26494)------------------------------
% 0.21/0.49  % (26480)Success in time 0.128 s
%------------------------------------------------------------------------------
