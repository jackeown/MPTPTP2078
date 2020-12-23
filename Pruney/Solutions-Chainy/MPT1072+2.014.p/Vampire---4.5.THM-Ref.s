%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 168 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  183 ( 837 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    ~ r1_tarski(k1_xboole_0,k1_funct_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f56,f61])).

fof(f61,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f33,f26])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X3,X0,X1)
                      & v1_funct_1(X3) )
                   => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(f33,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f24,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f45,f22])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f23,f55])).

fof(f55,plain,(
    k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f43,f22])).

fof(f43,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK0)
      | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f42,f26])).

fof(f42,plain,(
    ! [X1] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK0)
      | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f37,f20])).

fof(f37,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK0)
      | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(resolution,[],[f21,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f23,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ~ r1_tarski(sK1,k1_funct_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f52,f55])).

fof(f52,plain,(
    ~ r1_tarski(sK1,k3_funct_2(sK0,sK1,sK3,sK2)) ),
    inference(resolution,[],[f50,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f50,plain,(
    r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),sK1) ),
    inference(subsumption_resolution,[],[f49,f25])).

fof(f25,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),sK1) ),
    inference(resolution,[],[f48,f29])).

fof(f48,plain,(
    m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f40,f22])).

fof(f40,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1) ) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (28981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28982)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (28979)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (28999)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (28985)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (28994)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.50  % (28998)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (28980)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (28998)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f70,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k1_funct_1(sK3,sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f56,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    k1_xboole_0 = sK1),
% 0.20/0.50    inference(resolution,[],[f59,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | k1_xboole_0 = sK1),
% 0.20/0.50    inference(resolution,[],[f46,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    r2_hidden(sK2,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f33,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    v1_xboole_0(sK0) | r2_hidden(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f24,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    m1_subset_1(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(sK0,sK1,sK3))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f45,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X2,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(sK0,sK1,sK3))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f38,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X2,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(sK0,sK1,sK3))) )),
% 0.20/0.50    inference(resolution,[],[f21,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.50    inference(backward_demodulation,[],[f23,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2)),
% 0.20/0.50    inference(resolution,[],[f44,f24])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f43,f22])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f42,f26])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X1] : (v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f37,f20])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.20/0.50    inference(resolution,[],[f21,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k1_funct_1(sK3,sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f52,f55])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k3_funct_2(sK0,sK1,sK3,sK2))),
% 0.20/0.50    inference(resolution,[],[f50,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f49,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),sK1)),
% 0.20/0.50    inference(resolution,[],[f48,f29])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1)),
% 0.20/0.50    inference(resolution,[],[f41,f24])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f40,f22])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f39,f26])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f36,f20])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | m1_subset_1(k3_funct_2(sK0,sK1,sK3,X0),sK1)) )),
% 0.20/0.50    inference(resolution,[],[f21,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  % (28981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (28998)------------------------------
% 0.20/0.50  % (28998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28998)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (28998)Memory used [KB]: 6140
% 0.20/0.50  % (28998)Time elapsed: 0.080 s
% 0.20/0.50  % (28998)------------------------------
% 0.20/0.50  % (28998)------------------------------
% 0.20/0.51  % (28986)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (28981)Refutation not found, incomplete strategy% (28981)------------------------------
% 0.20/0.51  % (28981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28981)Memory used [KB]: 10490
% 0.20/0.51  % (28981)Time elapsed: 0.093 s
% 0.20/0.51  % (28981)------------------------------
% 0.20/0.51  % (28981)------------------------------
% 0.20/0.51  % (28977)Success in time 0.148 s
%------------------------------------------------------------------------------
