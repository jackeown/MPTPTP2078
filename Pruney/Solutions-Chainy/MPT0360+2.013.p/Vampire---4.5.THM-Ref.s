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
% DateTime   : Thu Dec  3 12:44:50 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 154 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   20
%              Number of atoms          :  118 ( 437 expanded)
%              Number of equality atoms :   29 ( 101 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(resolution,[],[f336,f148])).

fof(f148,plain,(
    r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f145,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f145,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f113,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f113,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(sK4(sK1,sK2),sK1) ) ),
    inference(forward_demodulation,[],[f112,f65])).

fof(f65,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(sK4(sK1,sK2),k3_xboole_0(sK1,sK2)) ) ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f54,f65])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f336,plain,(
    ! [X1] : ~ r2_hidden(X1,sK1) ),
    inference(forward_demodulation,[],[f335,f90])).

fof(f90,plain,(
    sK1 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f39,f66])).

fof(f66,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f37,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f335,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f334,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f334,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f331,f54])).

fof(f331,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f328,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f328,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK2)
    | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f317,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f317,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f187,f53])).

fof(f187,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f185,f46])).

fof(f185,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f180,f54])).

fof(f180,plain,(
    r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f45,f130])).

fof(f130,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f129,f93])).

fof(f93,plain,(
    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f129,plain,(
    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f47,f90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:28:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (791805952)
% 0.15/0.37  ipcrm: permission denied for id (795312130)
% 0.15/0.37  ipcrm: permission denied for id (791904261)
% 0.15/0.38  ipcrm: permission denied for id (791937030)
% 0.15/0.38  ipcrm: permission denied for id (795410439)
% 0.15/0.38  ipcrm: permission denied for id (792002568)
% 0.15/0.38  ipcrm: permission denied for id (795475978)
% 0.15/0.38  ipcrm: permission denied for id (795508747)
% 0.22/0.39  ipcrm: permission denied for id (795607054)
% 0.22/0.39  ipcrm: permission denied for id (795639823)
% 0.22/0.39  ipcrm: permission denied for id (792199184)
% 0.22/0.39  ipcrm: permission denied for id (795672593)
% 0.22/0.39  ipcrm: permission denied for id (792264722)
% 0.22/0.39  ipcrm: permission denied for id (792297491)
% 0.22/0.39  ipcrm: permission denied for id (792330260)
% 0.22/0.39  ipcrm: permission denied for id (795705365)
% 0.22/0.40  ipcrm: permission denied for id (792395798)
% 0.22/0.40  ipcrm: permission denied for id (792428568)
% 0.22/0.40  ipcrm: permission denied for id (795770905)
% 0.22/0.40  ipcrm: permission denied for id (795803674)
% 0.22/0.40  ipcrm: permission denied for id (795836443)
% 0.22/0.40  ipcrm: permission denied for id (792526876)
% 0.22/0.41  ipcrm: permission denied for id (792592415)
% 0.22/0.41  ipcrm: permission denied for id (792625184)
% 0.22/0.41  ipcrm: permission denied for id (795934753)
% 0.22/0.41  ipcrm: permission denied for id (792723491)
% 0.22/0.41  ipcrm: permission denied for id (796000292)
% 0.22/0.42  ipcrm: permission denied for id (792854567)
% 0.22/0.42  ipcrm: permission denied for id (792920104)
% 0.22/0.42  ipcrm: permission denied for id (792952873)
% 0.22/0.42  ipcrm: permission denied for id (793018411)
% 0.22/0.42  ipcrm: permission denied for id (793051180)
% 0.22/0.42  ipcrm: permission denied for id (796131373)
% 0.22/0.43  ipcrm: permission denied for id (796164142)
% 0.22/0.43  ipcrm: permission denied for id (793149487)
% 0.22/0.43  ipcrm: permission denied for id (796229681)
% 0.22/0.43  ipcrm: permission denied for id (796262450)
% 0.22/0.43  ipcrm: permission denied for id (793247796)
% 0.22/0.44  ipcrm: permission denied for id (793280566)
% 0.22/0.44  ipcrm: permission denied for id (793313335)
% 0.22/0.44  ipcrm: permission denied for id (793346105)
% 0.22/0.44  ipcrm: permission denied for id (796393530)
% 0.22/0.44  ipcrm: permission denied for id (793411643)
% 0.22/0.44  ipcrm: permission denied for id (796426300)
% 0.22/0.45  ipcrm: permission denied for id (793477181)
% 0.22/0.45  ipcrm: permission denied for id (793509950)
% 0.22/0.45  ipcrm: permission denied for id (793542719)
% 0.22/0.45  ipcrm: permission denied for id (796459072)
% 0.22/0.45  ipcrm: permission denied for id (796491841)
% 0.22/0.45  ipcrm: permission denied for id (796524610)
% 0.22/0.45  ipcrm: permission denied for id (796557379)
% 0.22/0.45  ipcrm: permission denied for id (796590148)
% 0.22/0.46  ipcrm: permission denied for id (793673798)
% 0.22/0.46  ipcrm: permission denied for id (796655687)
% 0.22/0.46  ipcrm: permission denied for id (796688456)
% 0.22/0.46  ipcrm: permission denied for id (793739337)
% 0.22/0.46  ipcrm: permission denied for id (793804875)
% 0.22/0.46  ipcrm: permission denied for id (793837644)
% 0.22/0.47  ipcrm: permission denied for id (796786766)
% 0.22/0.47  ipcrm: permission denied for id (793935952)
% 0.22/0.47  ipcrm: permission denied for id (794001490)
% 0.22/0.47  ipcrm: permission denied for id (794034259)
% 0.22/0.47  ipcrm: permission denied for id (794067028)
% 0.22/0.48  ipcrm: permission denied for id (796917846)
% 0.22/0.48  ipcrm: permission denied for id (794132567)
% 0.22/0.48  ipcrm: permission denied for id (794198105)
% 0.22/0.48  ipcrm: permission denied for id (794263644)
% 0.22/0.48  ipcrm: permission denied for id (794296413)
% 0.22/0.49  ipcrm: permission denied for id (794329182)
% 0.22/0.49  ipcrm: permission denied for id (794394720)
% 0.22/0.49  ipcrm: permission denied for id (794460260)
% 0.22/0.49  ipcrm: permission denied for id (797180005)
% 0.22/0.50  ipcrm: permission denied for id (797212774)
% 0.22/0.50  ipcrm: permission denied for id (794558567)
% 0.22/0.50  ipcrm: permission denied for id (794624104)
% 0.22/0.50  ipcrm: permission denied for id (794656873)
% 0.22/0.50  ipcrm: permission denied for id (794722411)
% 0.22/0.50  ipcrm: permission denied for id (794755180)
% 0.22/0.51  ipcrm: permission denied for id (797278317)
% 0.22/0.51  ipcrm: permission denied for id (794787950)
% 0.22/0.51  ipcrm: permission denied for id (797311087)
% 0.22/0.51  ipcrm: permission denied for id (794820720)
% 0.22/0.51  ipcrm: permission denied for id (794853489)
% 0.22/0.51  ipcrm: permission denied for id (794984565)
% 0.22/0.52  ipcrm: permission denied for id (795017334)
% 0.22/0.52  ipcrm: permission denied for id (797474936)
% 0.22/0.52  ipcrm: permission denied for id (797507705)
% 0.22/0.52  ipcrm: permission denied for id (795082874)
% 0.22/0.52  ipcrm: permission denied for id (795148412)
% 0.22/0.52  ipcrm: permission denied for id (797573245)
% 0.39/0.65  % (3696)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.39/0.68  % (3718)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.39/0.68  % (3718)Refutation found. Thanks to Tanya!
% 0.39/0.68  % SZS status Theorem for theBenchmark
% 0.39/0.68  % (3703)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.39/0.68  % (3710)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.39/0.69  % (3706)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.39/0.70  % (3715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.39/0.70  % (3695)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.39/0.70  % (3707)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.70  % (3697)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.39/0.70  % (3710)Refutation not found, incomplete strategy% (3710)------------------------------
% 0.39/0.70  % (3710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (3710)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.70  
% 0.39/0.70  % (3710)Memory used [KB]: 6140
% 0.39/0.70  % (3710)Time elapsed: 0.131 s
% 0.39/0.70  % (3710)------------------------------
% 0.39/0.70  % (3710)------------------------------
% 0.39/0.70  % (3699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.39/0.70  % (3704)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.39/0.70  % SZS output start Proof for theBenchmark
% 0.39/0.70  fof(f340,plain,(
% 0.39/0.70    $false),
% 0.39/0.70    inference(resolution,[],[f336,f148])).
% 0.39/0.70  fof(f148,plain,(
% 0.39/0.70    r2_hidden(sK4(sK1,sK2),sK1)),
% 0.39/0.70    inference(subsumption_resolution,[],[f145,f40])).
% 0.39/0.70  fof(f40,plain,(
% 0.39/0.70    k1_xboole_0 != sK1),
% 0.39/0.70    inference(cnf_transformation,[],[f27])).
% 0.39/0.70  fof(f27,plain,(
% 0.39/0.70    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.39/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26])).
% 0.39/0.70  fof(f26,plain,(
% 0.39/0.70    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.39/0.70    introduced(choice_axiom,[])).
% 0.39/0.70  fof(f19,plain,(
% 0.39/0.70    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.39/0.70    inference(flattening,[],[f18])).
% 0.39/0.70  fof(f18,plain,(
% 0.39/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.39/0.70    inference(ennf_transformation,[],[f16])).
% 0.39/0.70  fof(f16,negated_conjecture,(
% 0.39/0.70    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.39/0.70    inference(negated_conjecture,[],[f15])).
% 0.39/0.70  fof(f15,conjecture,(
% 0.39/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 0.39/0.70  fof(f145,plain,(
% 0.39/0.70    r2_hidden(sK4(sK1,sK2),sK1) | k1_xboole_0 = sK1),
% 0.39/0.70    inference(resolution,[],[f113,f44])).
% 0.39/0.70  fof(f44,plain,(
% 0.39/0.70    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.39/0.70    inference(cnf_transformation,[],[f29])).
% 0.39/0.70  fof(f29,plain,(
% 0.39/0.70    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.39/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f28])).
% 0.39/0.70  fof(f28,plain,(
% 0.39/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.39/0.70    introduced(choice_axiom,[])).
% 0.39/0.70  fof(f20,plain,(
% 0.39/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.39/0.70    inference(ennf_transformation,[],[f3])).
% 0.39/0.70  fof(f3,axiom,(
% 0.39/0.70    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.39/0.70  fof(f113,plain,(
% 0.39/0.70    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(sK4(sK1,sK2),sK1)) )),
% 0.39/0.70    inference(forward_demodulation,[],[f112,f65])).
% 0.39/0.70  fof(f65,plain,(
% 0.39/0.70    sK1 = k3_xboole_0(sK1,sK2)),
% 0.39/0.70    inference(resolution,[],[f38,f55])).
% 0.39/0.70  fof(f55,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f23])).
% 0.39/0.70  fof(f23,plain,(
% 0.39/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.39/0.70    inference(ennf_transformation,[],[f5])).
% 0.39/0.70  fof(f5,axiom,(
% 0.39/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.39/0.70  fof(f38,plain,(
% 0.39/0.70    r1_tarski(sK1,sK2)),
% 0.39/0.70    inference(cnf_transformation,[],[f27])).
% 0.39/0.70  fof(f112,plain,(
% 0.39/0.70    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(sK4(sK1,sK2),k3_xboole_0(sK1,sK2))) )),
% 0.39/0.70    inference(resolution,[],[f92,f53])).
% 0.39/0.70  fof(f53,plain,(
% 0.39/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f32])).
% 0.39/0.70  fof(f32,plain,(
% 0.39/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.39/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f31])).
% 0.39/0.70  fof(f31,plain,(
% 0.39/0.70    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.39/0.70    introduced(choice_axiom,[])).
% 0.39/0.70  fof(f22,plain,(
% 0.39/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.39/0.70    inference(ennf_transformation,[],[f17])).
% 0.39/0.70  fof(f17,plain,(
% 0.39/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.70    inference(rectify,[],[f2])).
% 0.39/0.70  fof(f2,axiom,(
% 0.39/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.39/0.70  fof(f92,plain,(
% 0.39/0.70    ( ! [X0] : (~r1_xboole_0(sK1,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.39/0.70    inference(superposition,[],[f54,f65])).
% 0.39/0.70  fof(f54,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f32])).
% 0.39/0.70  fof(f336,plain,(
% 0.39/0.70    ( ! [X1] : (~r2_hidden(X1,sK1)) )),
% 0.39/0.70    inference(forward_demodulation,[],[f335,f90])).
% 0.39/0.70  fof(f90,plain,(
% 0.39/0.70    sK1 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.39/0.70    inference(resolution,[],[f71,f55])).
% 0.39/0.70  fof(f71,plain,(
% 0.39/0.70    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.39/0.70    inference(backward_demodulation,[],[f39,f66])).
% 0.39/0.70  fof(f66,plain,(
% 0.39/0.70    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.39/0.70    inference(resolution,[],[f37,f56])).
% 0.39/0.70  fof(f56,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f24])).
% 0.39/0.70  fof(f24,plain,(
% 0.39/0.70    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.70    inference(ennf_transformation,[],[f13])).
% 0.39/0.70  fof(f13,axiom,(
% 0.39/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.39/0.70  fof(f37,plain,(
% 0.39/0.70    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.39/0.70    inference(cnf_transformation,[],[f27])).
% 0.39/0.70  fof(f39,plain,(
% 0.39/0.70    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.39/0.70    inference(cnf_transformation,[],[f27])).
% 0.39/0.70  fof(f335,plain,(
% 0.39/0.70    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) )),
% 0.39/0.70    inference(forward_demodulation,[],[f334,f46])).
% 0.39/0.70  fof(f46,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f1])).
% 0.39/0.70  fof(f1,axiom,(
% 0.39/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.39/0.70  fof(f334,plain,(
% 0.39/0.70    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))) )),
% 0.39/0.70    inference(resolution,[],[f331,f54])).
% 0.39/0.70  fof(f331,plain,(
% 0.39/0.70    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.39/0.70    inference(subsumption_resolution,[],[f328,f45])).
% 0.39/0.70  fof(f45,plain,(
% 0.39/0.70    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f9])).
% 0.39/0.70  fof(f9,axiom,(
% 0.39/0.70    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.39/0.70  fof(f328,plain,(
% 0.39/0.70    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK2) | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.39/0.70    inference(resolution,[],[f317,f61])).
% 0.39/0.70  fof(f61,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f25])).
% 0.39/0.70  fof(f25,plain,(
% 0.39/0.70    ! [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1))),
% 0.39/0.70    inference(ennf_transformation,[],[f10])).
% 0.39/0.70  fof(f10,axiom,(
% 0.39/0.70    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.39/0.70  fof(f317,plain,(
% 0.39/0.70    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 0.39/0.70    inference(resolution,[],[f187,f53])).
% 0.39/0.70  fof(f187,plain,(
% 0.39/0.70    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))) )),
% 0.39/0.70    inference(forward_demodulation,[],[f185,f46])).
% 0.39/0.70  fof(f185,plain,(
% 0.39/0.70    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)))) )),
% 0.39/0.70    inference(resolution,[],[f180,f54])).
% 0.39/0.70  fof(f180,plain,(
% 0.39/0.70    r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))),
% 0.39/0.70    inference(superposition,[],[f45,f130])).
% 0.39/0.70  fof(f130,plain,(
% 0.39/0.70    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.39/0.70    inference(forward_demodulation,[],[f129,f93])).
% 0.39/0.70  fof(f93,plain,(
% 0.39/0.70    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1)),
% 0.39/0.70    inference(superposition,[],[f47,f65])).
% 0.39/0.70  fof(f47,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f4])).
% 0.39/0.70  fof(f4,axiom,(
% 0.39/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.39/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.39/0.70  fof(f129,plain,(
% 0.39/0.70    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.39/0.70    inference(superposition,[],[f47,f90])).
% 0.39/0.70  % SZS output end Proof for theBenchmark
% 0.39/0.70  % (3718)------------------------------
% 0.39/0.70  % (3718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (3718)Termination reason: Refutation
% 0.39/0.70  
% 0.39/0.70  % (3718)Memory used [KB]: 1918
% 0.39/0.70  % (3718)Time elapsed: 0.116 s
% 0.39/0.70  % (3718)------------------------------
% 0.39/0.70  % (3718)------------------------------
% 0.39/0.70  % (3539)Success in time 0.339 s
%------------------------------------------------------------------------------
