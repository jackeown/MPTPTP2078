%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 192 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  196 ( 822 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f51])).

fof(f51,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f139,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f138,f126])).

fof(f126,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f125,f88])).

fof(f88,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f27,f83])).

fof(f83,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK2,sK0,sK3,X0) ),
    inference(resolution,[],[f49,f29])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f27,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f125,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK5,sK1) ),
    inference(factoring,[],[f120])).

fof(f120,plain,(
    ! [X4] :
      ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | r2_hidden(sK4,k9_relat_1(sK3,X4))
      | ~ r2_hidden(sK5,X4) ) ),
    inference(subsumption_resolution,[],[f118,f51])).

fof(f118,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK5,X4)
      | r2_hidden(sK4,k9_relat_1(sK3,X4))
      | r2_hidden(sK4,k9_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f50,f87])).

fof(f87,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(backward_demodulation,[],[f26,f83])).

fof(f26,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f42,f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f138,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f136,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f135,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1,sK3),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f77,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f77,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK6(X10,X11,sK3),sK2)
      | ~ r2_hidden(X10,k9_relat_1(sK3,X11)) ) ),
    inference(subsumption_resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(X10,k9_relat_1(sK3,X11))
      | r2_hidden(sK6(X10,X11,sK3),sK2) ) ),
    inference(resolution,[],[f40,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f46,f62])).

fof(f62,plain,(
    sK3 = k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(subsumption_resolution,[],[f61,f51])).

fof(f61,plain,
    ( sK3 = k5_relat_1(k6_relat_1(sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | k5_relat_1(k6_relat_1(X1),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(X1),X0) = X0
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f134,f51])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f133,f40])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f85,f126])).

fof(f85,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f24,f83])).

fof(f24,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:07:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (11327)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.45  % (11319)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (11318)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.46  % (11325)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.47  % (11325)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (11319)Refutation not found, incomplete strategy% (11319)------------------------------
% 0.21/0.47  % (11319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (11319)Memory used [KB]: 6140
% 0.21/0.47  % (11319)Time elapsed: 0.067 s
% 0.21/0.47  % (11319)------------------------------
% 0.21/0.47  % (11319)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f43,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~v1_relat_1(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(backward_demodulation,[],[f27,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK2,sK0,sK3,X0)) )),
% 0.21/0.48    inference(resolution,[],[f49,f29])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(factoring,[],[f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X4] : (r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK4,k9_relat_1(sK3,X4)) | ~r2_hidden(sK5,X4)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f51])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X4] : (~v1_relat_1(sK3) | ~r2_hidden(sK5,X4) | r2_hidden(sK4,k9_relat_1(sK3,X4)) | r2_hidden(sK4,k9_relat_1(sK3,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f50,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.48    inference(backward_demodulation,[],[f26,f83])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.48    inference(resolution,[],[f136,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1,sK3),sK2) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) )),
% 0.21/0.48    inference(resolution,[],[f77,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X10,X11] : (r2_hidden(sK6(X10,X11,sK3),sK2) | ~r2_hidden(X10,k9_relat_1(sK3,X11))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f51])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X10,X11] : (~v1_relat_1(sK3) | ~r2_hidden(X10,k9_relat_1(sK3,X11)) | r2_hidden(sK6(X10,X11,sK3),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f40,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f51])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK2) | ~v1_relat_1(sK3)) )),
% 0.21/0.48    inference(superposition,[],[f46,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    sK3 = k5_relat_1(k6_relat_1(sK2),sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f51])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    sK3 = k5_relat_1(k6_relat_1(sK2),sK3) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f60,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    v4_relat_1(sK3,sK2)),
% 0.21/0.48    inference(resolution,[],[f44,f29])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_relat_1(X0,X1) | k5_relat_1(k6_relat_1(X1),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = X0 | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f33,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK6(sK4,X0,sK3),sK2) | ~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f51])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK6(sK4,X0,sK3),sK2) | ~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.48    inference(resolution,[],[f133,f40])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f85,f126])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X5] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f24,f83])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (11325)------------------------------
% 0.21/0.48  % (11325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (11325)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (11325)Memory used [KB]: 6268
% 0.21/0.48  % (11325)Time elapsed: 0.056 s
% 0.21/0.48  % (11325)------------------------------
% 0.21/0.48  % (11325)------------------------------
% 0.21/0.48  % (11311)Success in time 0.13 s
%------------------------------------------------------------------------------
