%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0766+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:37 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 228 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 (1448 expanded)
%              Number of equality atoms :   30 ( 132 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f134,f62])).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f54,f58])).

fof(f58,plain,(
    o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f55,plain,(
    v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f54,plain,(
    ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

% (12230)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f134,plain,(
    r2_hidden(sK1,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f105,f133])).

fof(f133,plain,(
    o_0_0_xboole_0 = sK6(sK0,sK1) ),
    inference(resolution,[],[f132,f105])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK6(sK0,X1))
      | o_0_0_xboole_0 = sK6(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f131,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(sK6(sK0,X0),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( r1_tarski(sK6(sK0,X0),k3_relat_1(sK0))
      | r1_tarski(sK6(sK0,X0),k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK7(sK6(sK0,X1),X2),k3_relat_1(sK0))
      | r1_tarski(sK6(sK0,X1),X2) ) ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK6(sK0,X1))
      | r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord1)).

% (12243)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (12221)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (12223)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (12249)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (12231)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (12244)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (12235)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(f131,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK6(sK0,X1))
      | ~ r1_tarski(sK6(sK0,X1),k3_relat_1(sK0))
      | o_0_0_xboole_0 = sK6(sK0,X1) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK6(sK0,X1))
      | ~ r1_tarski(sK6(sK0,X1),k3_relat_1(sK0))
      | o_0_0_xboole_0 = sK6(sK0,X1)
      | o_0_0_xboole_0 = sK6(sK0,X1)
      | ~ r1_tarski(sK6(sK0,X1),k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f128,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0),X0)
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f87,f31])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | o_0_0_xboole_0 = X0
      | r2_hidden(sK4(sK0,X0),X0) ) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | o_0_0_xboole_0 = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(f128,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK4(sK0,X1),sK6(sK0,X2))
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | o_0_0_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f127,f31])).

fof(f127,plain,(
    ! [X2,X1] :
      ( o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(sK4(sK0,X1),sK6(sK0,X2)) ) ),
    inference(resolution,[],[f125,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(sK0,X0),X1),sK0)
      | o_0_0_xboole_0 = X0
      | ~ r2_hidden(X1,X0)
      | ~ r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f124,f31])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | o_0_0_xboole_0 = X0
      | ~ r2_hidden(X1,X0)
      | r2_hidden(k4_tarski(sK4(sK0,X0),X1),sK0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f105,plain,(
    r2_hidden(sK1,sK6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f30])).

% (12238)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f30,plain,(
    r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK0))
    | r2_hidden(sK1,sK6(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK0))
    | r2_hidden(sK1,sK6(sK0,sK1))
    | ~ r2_hidden(sK1,k3_relat_1(sK0))
    | r2_hidden(sK1,sK6(sK0,sK1)) ),
    inference(resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK3(X0)),sK0)
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | r2_hidden(sK1,sK6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f76,f30])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k3_relat_1(sK0))
      | r2_hidden(sK1,sK6(sK0,X0))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK3(X0)),sK0) ) ),
    inference(resolution,[],[f74,f27])).

fof(f27,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X2,sK3(X2)),sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | r2_hidden(X0,sK6(sK0,X1)) ) ),
    inference(resolution,[],[f41,f31])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,sK6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK1,sK3(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0))
      | r2_hidden(sK1,sK6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k3_relat_1(sK0))
      | r2_hidden(sK1,sK6(sK0,X1))
      | ~ r2_hidden(X1,k3_relat_1(sK0))
      | r2_hidden(k4_tarski(sK1,sK3(X1)),sK0) ) ),
    inference(resolution,[],[f74,f25])).

fof(f25,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0))
      | r2_hidden(k4_tarski(sK1,sK3(X2)),sK0) ) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
