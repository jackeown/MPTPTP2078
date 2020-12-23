%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:12 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 488 expanded)
%              Number of leaves         :    6 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 (3358 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(resolution,[],[f74,f56])).

fof(f56,plain,(
    ~ r2_hidden(sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f20,plain,(
    ~ r1_tarski(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                       => ( r1_tarski(X3,X4)
                         => r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                     => ( r1_tarski(X3,X4)
                       => r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_funct_2)).

fof(f74,plain,(
    r2_hidden(sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(forward_demodulation,[],[f73,f64])).

fof(f64,plain,(
    sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)) = k8_relset_1(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK3,sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)))) ),
    inference(unit_resulting_resolution,[],[f26,f25,f22,f23,f21,f24,f53,f55,f58,f44])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X1,X2,sK8(X0,X1,X2,X3,X5)) = X5
      | ~ r2_hidden(X5,k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X1,X2,sK8(X0,X1,X2,X3,X5)) = X5
      | ~ r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
                     => ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(X0))
                           => ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_funct_2)).

fof(f58,plain,(
    m1_subset_1(sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f55,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f55,plain,(
    r2_hidden(sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f26,f22,f25,f21,f23,f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    r2_hidden(k8_relset_1(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK3,sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)))),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f22,f23,f18,f24,f52,f66,f54,f62,f43])).

fof(f43,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k8_relset_1(X0,X1,X2,X6),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ r2_hidden(X6,X3)
      | r2_hidden(k8_relset_1(X0,X1,X2,X6),k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k8_relset_1(X0,X1,X2,X6),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ r2_hidden(X6,X3)
      | r2_hidden(k8_relset_1(X0,X1,X2,X6),X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(equality_resolution,[],[f36])).

% (8495)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (8495)Refutation not found, incomplete strategy% (8495)------------------------------
% (8495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8487)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (8512)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (8492)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (8498)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (8493)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (8506)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (8511)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ r2_hidden(X6,X3)
      | k8_relset_1(X0,X1,X2,X6) != X5
      | r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f17])).

% (8503)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (8508)Refutation not found, incomplete strategy% (8508)------------------------------
% (8508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f62,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f26,f25,f23,f21,f24,f53,f55,f58,f46])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X5),k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X5,k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | m1_subset_1(sK8(X0,X1,X2,X3,X5),k1_zfmisc_1(X1))
      | ~ r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

% (8513)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f66,plain,(
    r2_hidden(sK8(sK0,sK1,sK2,sK3,sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),sK4) ),
    inference(unit_resulting_resolution,[],[f19,f63,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    r2_hidden(sK8(sK0,sK1,sK2,sK3,sK5(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),sK3) ),
    inference(unit_resulting_resolution,[],[f26,f25,f22,f23,f21,f24,f53,f55,f58,f45])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | r2_hidden(sK8(X0,X1,X2,X3,X5),X3)
      | ~ r2_hidden(X5,k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | r2_hidden(sK8(X0,X1,X2,X3,X5),X3)
      | ~ r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK4),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f26,f22,f25,f18,f23,f24,f27])).

fof(f18,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
