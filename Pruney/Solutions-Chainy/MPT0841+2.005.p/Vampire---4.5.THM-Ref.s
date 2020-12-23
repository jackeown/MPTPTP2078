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
% DateTime   : Thu Dec  3 12:57:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 163 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 714 expanded)
%              Number of equality atoms :    4 (  20 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(subsumption_resolution,[],[f383,f57])).

fof(f57,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f383,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f382,f340])).

fof(f340,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f339,f167])).

fof(f167,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f25,f160])).

fof(f160,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK2,sK0,sK3,X0) ),
    inference(resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f25,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f339,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK5,sK1) ),
    inference(factoring,[],[f305])).

fof(f305,plain,(
    ! [X9] :
      ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | r2_hidden(sK4,k9_relat_1(sK3,X9))
      | ~ r2_hidden(sK5,X9) ) ),
    inference(subsumption_resolution,[],[f301,f57])).

fof(f301,plain,(
    ! [X9] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK5,X9)
      | r2_hidden(sK4,k9_relat_1(sK3,X9))
      | r2_hidden(sK4,k9_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f47,f166])).

fof(f166,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(backward_demodulation,[],[f24,f160])).

fof(f24,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f382,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f380,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f380,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f379,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1,sK3),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f130,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f130,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK7(X10,X11,sK3),sK2)
      | ~ r2_hidden(X10,k9_relat_1(sK3,X11)) ) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f117,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(X10,k9_relat_1(sK3,X11))
      | r2_hidden(sK7(X10,X11,sK3),sK2) ) ),
    inference(resolution,[],[f39,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f379,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK7(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f378,f57])).

fof(f378,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK7(sK4,X0,sK3),sK1)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f376,f39])).

fof(f376,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f164,f340])).

fof(f164,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f22,f160])).

fof(f22,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (22994)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (22995)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (23011)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (22994)Refutation not found, incomplete strategy% (22994)------------------------------
% 0.21/0.50  % (22994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23015)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (22992)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (23006)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (23012)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (22998)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (23009)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (23010)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (23007)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (22996)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (23004)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (22994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22994)Memory used [KB]: 10618
% 0.21/0.51  % (22994)Time elapsed: 0.087 s
% 0.21/0.51  % (22994)------------------------------
% 0.21/0.51  % (22994)------------------------------
% 0.21/0.51  % (23003)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (23014)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (22991)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (22993)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (23002)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (22997)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (23000)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (22999)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (23005)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (23001)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.53  % (23013)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.54  % (23004)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f384,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f383,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f42,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f382,f340])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f339,f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f25,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK2,sK0,sK3,X0)) )),
% 0.21/0.54    inference(resolution,[],[f43,f27])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK5,sK1)),
% 0.21/0.54    inference(factoring,[],[f305])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ( ! [X9] : (r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK4,k9_relat_1(sK3,X9)) | ~r2_hidden(sK5,X9)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f301,f57])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    ( ! [X9] : (~v1_relat_1(sK3) | ~r2_hidden(sK5,X9) | r2_hidden(sK4,k9_relat_1(sK3,X9)) | r2_hidden(sK4,k9_relat_1(sK3,sK1))) )),
% 0.21/0.54    inference(resolution,[],[f47,f166])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.54    inference(backward_demodulation,[],[f24,f160])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f41,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f381])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.54    inference(resolution,[],[f380,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK7(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f379,f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(sK7(X0,X1,sK3),sK2) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) )),
% 0.21/0.54    inference(resolution,[],[f130,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X10,X11] : (r2_hidden(sK7(X10,X11,sK3),sK2) | ~r2_hidden(X10,k9_relat_1(sK3,X11))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f57])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X10,X11] : (~v1_relat_1(sK3) | ~r2_hidden(X10,k9_relat_1(sK3,X11)) | r2_hidden(sK7(X10,X11,sK3),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f39,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f44,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.54    inference(resolution,[],[f35,f27])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK7(sK4,X0,sK3),sK2) | ~r2_hidden(sK7(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f378,f57])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK7(sK4,X0,sK3),sK2) | ~r2_hidden(sK7(sK4,X0,sK3),sK1) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.54    inference(resolution,[],[f376,f39])).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.54    inference(resolution,[],[f164,f340])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X5] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f22,f160])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23004)------------------------------
% 0.21/0.54  % (23004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23004)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23004)Memory used [KB]: 6524
% 0.21/0.54  % (23004)Time elapsed: 0.121 s
% 0.21/0.54  % (23004)------------------------------
% 0.21/0.54  % (23004)------------------------------
% 0.21/0.54  % (22987)Success in time 0.178 s
%------------------------------------------------------------------------------
