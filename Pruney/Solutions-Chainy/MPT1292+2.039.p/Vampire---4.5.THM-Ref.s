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
% DateTime   : Thu Dec  3 13:13:16 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 116 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  169 ( 470 expanded)
%              Number of equality atoms :   30 (  98 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(resolution,[],[f84,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f84,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f83,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f83,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f82,f31])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

% (15988)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f82,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f37,f75])).

fof(f75,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f32,f34])).

fof(f34,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f63,f64])).

fof(f64,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK2(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK2(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f58,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f45,f35])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] : k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f63,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f62,f52])).

fof(f52,plain,(
    k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f40,f47])).

fof(f62,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f42,f46])).

fof(f46,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (15992)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (16000)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.48  % (15992)Refutation not found, incomplete strategy% (15992)------------------------------
% 0.20/0.48  % (15992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (15992)Memory used [KB]: 6140
% 0.20/0.48  % (15992)Time elapsed: 0.069 s
% 0.20/0.48  % (15992)------------------------------
% 0.20/0.48  % (15992)------------------------------
% 0.20/0.49  % (16001)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.49  % (16001)Refutation not found, incomplete strategy% (16001)------------------------------
% 0.20/0.49  % (16001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16001)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16001)Memory used [KB]: 1663
% 0.20/0.49  % (16001)Time elapsed: 0.066 s
% 0.20/0.49  % (16001)------------------------------
% 0.20/0.49  % (16001)------------------------------
% 0.20/0.49  % (15993)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (15990)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (15993)Refutation not found, incomplete strategy% (15993)------------------------------
% 0.20/0.50  % (15993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15993)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15993)Memory used [KB]: 10490
% 0.20/0.50  % (15993)Time elapsed: 0.078 s
% 0.20/0.50  % (15993)------------------------------
% 0.20/0.50  % (15993)------------------------------
% 0.20/0.50  % (15987)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (15986)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (15989)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (15994)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.23/0.51  % (15999)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.23/0.51  % (15996)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.23/0.52  % (15994)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  fof(f85,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(resolution,[],[f84,f35])).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    inference(cnf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    ~v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    inference(resolution,[],[f83,f30])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    ~v2_struct_0(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f26])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f13,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.23/0.52    inference(flattening,[],[f12])).
% 1.23/0.52  fof(f12,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f11])).
% 1.23/0.52  fof(f11,negated_conjecture,(
% 1.23/0.52    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.23/0.52    inference(negated_conjecture,[],[f10])).
% 1.23/0.52  fof(f10,conjecture,(
% 1.23/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 1.23/0.52  fof(f83,plain,(
% 1.23/0.52    v2_struct_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    inference(resolution,[],[f82,f31])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    l1_struct_0(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f26])).
% 1.23/0.52  % (15988)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.23/0.52  fof(f82,plain,(
% 1.23/0.52    ~l1_struct_0(sK0) | ~v1_xboole_0(k1_xboole_0) | v2_struct_0(sK0)),
% 1.23/0.52    inference(superposition,[],[f37,f75])).
% 1.23/0.52  fof(f75,plain,(
% 1.23/0.52    k1_xboole_0 = u1_struct_0(sK0)),
% 1.23/0.52    inference(resolution,[],[f72,f47])).
% 1.23/0.52  fof(f47,plain,(
% 1.23/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.23/0.52    inference(forward_demodulation,[],[f32,f34])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    k1_xboole_0 = sK1),
% 1.23/0.52    inference(cnf_transformation,[],[f26])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.23/0.52    inference(cnf_transformation,[],[f26])).
% 1.23/0.52  fof(f72,plain,(
% 1.23/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.23/0.52    inference(backward_demodulation,[],[f63,f64])).
% 1.23/0.52  fof(f64,plain,(
% 1.23/0.52    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.23/0.52    inference(resolution,[],[f58,f38])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f28])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK2(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f27])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK2(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK2(X0),X0)))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.23/0.52    inference(flattening,[],[f16])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.23/0.52    inference(ennf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,axiom,(
% 1.23/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.23/0.52  fof(f58,plain,(
% 1.23/0.52    ( ! [X0] : (~r2_hidden(X0,k3_tarski(k1_xboole_0))) )),
% 1.23/0.52    inference(resolution,[],[f57,f48])).
% 1.23/0.52  fof(f48,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.23/0.52    inference(resolution,[],[f45,f35])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f6])).
% 1.23/0.52  fof(f6,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.23/0.52  fof(f57,plain,(
% 1.23/0.52    ( ! [X0] : (m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f55,f53])).
% 1.23/0.52  fof(f53,plain,(
% 1.23/0.52    ( ! [X0] : (k3_tarski(k1_xboole_0) = k5_setfam_1(X0,k1_xboole_0)) )),
% 1.23/0.52    inference(resolution,[],[f40,f36])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = k3_tarski(X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.23/0.52    inference(ennf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 1.23/0.52  fof(f55,plain,(
% 1.23/0.52    ( ! [X0] : (m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(resolution,[],[f41,f36])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.23/0.52    inference(ennf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.23/0.52  fof(f63,plain,(
% 1.23/0.52    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.23/0.52    inference(forward_demodulation,[],[f62,f52])).
% 1.23/0.52  fof(f52,plain,(
% 1.23/0.52    k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) = k3_tarski(k1_xboole_0)),
% 1.23/0.52    inference(resolution,[],[f40,f47])).
% 1.23/0.52  fof(f62,plain,(
% 1.23/0.52    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.23/0.52    inference(resolution,[],[f42,f46])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 1.23/0.52    inference(forward_demodulation,[],[f33,f34])).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 1.23/0.52    inference(cnf_transformation,[],[f26])).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f29])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.23/0.52    inference(nnf_transformation,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.23/0.52    inference(ennf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,axiom,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.23/0.52    inference(flattening,[],[f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f9])).
% 1.23/0.52  fof(f9,axiom,(
% 1.23/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (15994)------------------------------
% 1.23/0.52  % (15994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (15994)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (15994)Memory used [KB]: 1663
% 1.23/0.52  % (15994)Time elapsed: 0.095 s
% 1.23/0.52  % (15994)------------------------------
% 1.23/0.52  % (15994)------------------------------
% 1.23/0.52  % (15988)Refutation not found, incomplete strategy% (15988)------------------------------
% 1.23/0.52  % (15988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (15988)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (15988)Memory used [KB]: 10618
% 1.23/0.52  % (15988)Time elapsed: 0.115 s
% 1.23/0.52  % (15985)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.23/0.52  % (15988)------------------------------
% 1.23/0.52  % (15988)------------------------------
% 1.23/0.52  % (15984)Success in time 0.154 s
%------------------------------------------------------------------------------
