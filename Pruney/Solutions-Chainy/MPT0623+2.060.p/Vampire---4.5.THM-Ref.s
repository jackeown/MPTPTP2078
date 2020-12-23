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
% DateTime   : Thu Dec  3 12:52:11 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 821 expanded)
%              Number of leaves         :    6 ( 200 expanded)
%              Depth                    :   24
%              Number of atoms          :  166 (3028 expanded)
%              Number of equality atoms :   61 (1134 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f698,plain,(
    $false ),
    inference(global_subsumption,[],[f612,f697])).

fof(f697,plain,(
    ! [X0] : sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f696,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f34,f36,f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f696,plain,(
    ! [X0] : sP3(X0,sK6(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f695,f94])).

fof(f94,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f55,f53,f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f53,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f36,f50])).

fof(f55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f34,f50])).

fof(f695,plain,(
    ! [X0] : sP3(X0,sK6(k2_relat_1(k1_xboole_0),X0)) ),
    inference(forward_demodulation,[],[f663,f50])).

fof(f663,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(k1_xboole_0,X1)),X0)) ),
    inference(backward_demodulation,[],[f139,f662])).

fof(f662,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f615])).

fof(f615,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f18,f613])).

fof(f613,plain,(
    k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f256,f588])).

fof(f588,plain,(
    ! [X0] : k1_xboole_0 = k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f246,f577,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f577,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f555,f558])).

fof(f558,plain,(
    ! [X2,X1] :
      ( ~ sP3(X2,k1_funct_1(k1_xboole_0,X1))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f246,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f33,f50])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f555,plain,(
    ! [X2,X1] :
      ( sP3(X1,k1_funct_1(k1_xboole_0,X2))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f139,f124])).

fof(f246,plain,(
    ! [X0,X1] : ~ sP3(X0,sK6(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f182,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ sP3(X2,sK6(X0,X1)) ) ),
    inference(superposition,[],[f24,f36])).

fof(f24,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f47,f180])).

fof(f180,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f150,f177])).

fof(f177,plain,(
    ! [X0,X1] : k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f152,f33])).

fof(f152,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f151,f36])).

fof(f151,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f141,f24])).

fof(f141,plain,(
    ! [X0] : sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f43,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] : r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f40,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f34,f36,f17])).

fof(f17,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f150,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f141,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f256,plain,(
    ! [X0] : sK0 = k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f182,f246,f28])).

fof(f18,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f139,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(sK1,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f43,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f126,f36])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f612,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f590,f50])).

fof(f590,plain,(
    ! [X0,X1] : ~ sP3(X0,sK6(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f577,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (31170)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.44  % (31148)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.48  % (31164)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.48  % (31156)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (31172)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (31155)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (31169)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (31145)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (31162)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (31147)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (31171)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (31161)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (31167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (31160)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (31146)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (31153)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (31163)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (31153)Refutation not found, incomplete strategy% (31153)------------------------------
% 0.22/0.53  % (31153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31153)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31153)Memory used [KB]: 10618
% 0.22/0.53  % (31153)Time elapsed: 0.117 s
% 0.22/0.53  % (31153)------------------------------
% 0.22/0.53  % (31153)------------------------------
% 0.22/0.53  % (31159)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (31155)Refutation not found, incomplete strategy% (31155)------------------------------
% 0.22/0.53  % (31155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31155)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31155)Memory used [KB]: 10618
% 0.22/0.53  % (31155)Time elapsed: 0.119 s
% 0.22/0.53  % (31155)------------------------------
% 0.22/0.53  % (31155)------------------------------
% 0.22/0.53  % (31152)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (31165)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (31147)Refutation not found, incomplete strategy% (31147)------------------------------
% 0.22/0.53  % (31147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31147)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31147)Memory used [KB]: 10618
% 0.22/0.53  % (31147)Time elapsed: 0.118 s
% 0.22/0.53  % (31147)------------------------------
% 0.22/0.53  % (31147)------------------------------
% 0.22/0.53  % (31151)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (31157)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (31145)Refutation not found, incomplete strategy% (31145)------------------------------
% 0.22/0.54  % (31145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31145)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31145)Memory used [KB]: 1663
% 0.22/0.54  % (31145)Time elapsed: 0.116 s
% 0.22/0.54  % (31145)------------------------------
% 0.22/0.54  % (31145)------------------------------
% 0.22/0.54  % (31162)Refutation not found, incomplete strategy% (31162)------------------------------
% 0.22/0.54  % (31162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31162)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31162)Memory used [KB]: 10618
% 0.22/0.54  % (31162)Time elapsed: 0.121 s
% 0.22/0.54  % (31162)------------------------------
% 0.22/0.54  % (31162)------------------------------
% 0.22/0.54  % (31149)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (31166)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (31168)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (31167)Refutation not found, incomplete strategy% (31167)------------------------------
% 0.22/0.55  % (31167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31167)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31167)Memory used [KB]: 10618
% 0.22/0.55  % (31167)Time elapsed: 0.132 s
% 0.22/0.55  % (31167)------------------------------
% 0.22/0.55  % (31167)------------------------------
% 0.22/0.55  % (31173)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (31165)Refutation not found, incomplete strategy% (31165)------------------------------
% 0.22/0.55  % (31165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31165)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31165)Memory used [KB]: 10746
% 0.22/0.55  % (31165)Time elapsed: 0.123 s
% 0.22/0.55  % (31165)------------------------------
% 0.22/0.55  % (31165)------------------------------
% 0.22/0.55  % (31174)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.56  % (31169)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f698,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(global_subsumption,[],[f612,f697])).
% 1.50/0.56  fof(f697,plain,(
% 1.50/0.56    ( ! [X0] : (sP3(X0,k1_xboole_0)) )),
% 1.50/0.56    inference(forward_demodulation,[],[f696,f50])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f34,f36,f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,plain,(
% 1.50/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(flattening,[],[f10])).
% 1.50/0.56  fof(f10,plain,(
% 1.50/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,plain,(
% 1.50/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f696,plain,(
% 1.50/0.56    ( ! [X0] : (sP3(X0,sK6(k1_xboole_0,X0))) )),
% 1.50/0.56    inference(forward_demodulation,[],[f695,f94])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f55,f53,f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,plain,(
% 1.50/0.56    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.50/0.56    inference(superposition,[],[f36,f50])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    v1_relat_1(k1_xboole_0)),
% 1.50/0.56    inference(superposition,[],[f34,f50])).
% 1.50/0.56  fof(f695,plain,(
% 1.50/0.56    ( ! [X0] : (sP3(X0,sK6(k2_relat_1(k1_xboole_0),X0))) )),
% 1.50/0.56    inference(forward_demodulation,[],[f663,f50])).
% 1.50/0.56  fof(f663,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k1_xboole_0,X1)),X0))) )),
% 1.50/0.56    inference(backward_demodulation,[],[f139,f662])).
% 1.50/0.56  fof(f662,plain,(
% 1.50/0.56    k1_xboole_0 = sK1),
% 1.50/0.56    inference(trivial_inequality_removal,[],[f615])).
% 1.50/0.56  fof(f615,plain,(
% 1.50/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.50/0.56    inference(backward_demodulation,[],[f18,f613])).
% 1.50/0.56  fof(f613,plain,(
% 1.50/0.56    k1_xboole_0 = sK0),
% 1.50/0.56    inference(backward_demodulation,[],[f256,f588])).
% 1.50/0.56  fof(f588,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X0))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f34,f35,f246,f577,f28])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f14,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(flattening,[],[f13])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.50/0.56  fof(f577,plain,(
% 1.50/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.50/0.56    inference(global_subsumption,[],[f555,f558])).
% 1.50/0.56  fof(f558,plain,(
% 1.50/0.56    ( ! [X2,X1] : (~sP3(X2,k1_funct_1(k1_xboole_0,X1)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.50/0.56    inference(superposition,[],[f246,f124])).
% 1.50/0.56  fof(f124,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.50/0.56    inference(superposition,[],[f33,f50])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f555,plain,(
% 1.50/0.56    ( ! [X2,X1] : (sP3(X1,k1_funct_1(k1_xboole_0,X2)) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.50/0.56    inference(superposition,[],[f139,f124])).
% 1.50/0.56  fof(f246,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~sP3(X0,sK6(sK0,X1))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f182,f56])).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~sP3(X2,sK6(X0,X1))) )),
% 1.50/0.56    inference(superposition,[],[f24,f36])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f182,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.50/0.56    inference(backward_demodulation,[],[f47,f180])).
% 1.50/0.56  fof(f180,plain,(
% 1.50/0.56    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 1.50/0.56    inference(backward_demodulation,[],[f150,f177])).
% 1.50/0.56  fof(f177,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f152,f33])).
% 1.50/0.56  fof(f152,plain,(
% 1.50/0.56    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1)) )),
% 1.50/0.56    inference(forward_demodulation,[],[f151,f36])).
% 1.50/0.56  fof(f151,plain,(
% 1.50/0.56    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0)))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f141,f24])).
% 1.50/0.56  fof(f141,plain,(
% 1.50/0.56    ( ! [X0] : (sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f34,f35,f43,f37])).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ( ! [X0] : (r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0)))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f40,f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,plain,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f35,f34,f36,f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,plain,(
% 1.50/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.50/0.56    inference(flattening,[],[f8])).
% 1.50/0.56  fof(f8,plain,(
% 1.50/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.50/0.56    inference(negated_conjecture,[],[f6])).
% 1.50/0.56  fof(f6,conjecture,(
% 1.50/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.50/0.56  fof(f150,plain,(
% 1.50/0.56    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f141,f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0)) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f40,f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f15])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f256,plain,(
% 1.50/0.56    ( ! [X0] : (sK0 = k2_relat_1(sK6(sK0,X0))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f34,f35,f182,f246,f28])).
% 1.50/0.56  fof(f18,plain,(
% 1.50/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.50/0.56    inference(cnf_transformation,[],[f9])).
% 1.50/0.56  fof(f139,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(sK1,X1)),X0))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f43,f129])).
% 1.50/0.56  fof(f129,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f128])).
% 1.50/0.56  fof(f128,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.50/0.56    inference(forward_demodulation,[],[f126,f36])).
% 1.50/0.56  fof(f126,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.50/0.56    inference(superposition,[],[f39,f33])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.50/0.56    inference(equality_resolution,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f612,plain,(
% 1.50/0.56    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 1.50/0.56    inference(forward_demodulation,[],[f590,f50])).
% 1.50/0.56  fof(f590,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~sP3(X0,sK6(k1_xboole_0,X1))) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f577,f56])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (31169)------------------------------
% 1.50/0.56  % (31169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (31169)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (31169)Memory used [KB]: 6652
% 1.50/0.56  % (31169)Time elapsed: 0.150 s
% 1.50/0.56  % (31169)------------------------------
% 1.50/0.56  % (31169)------------------------------
% 1.50/0.56  % (31144)Success in time 0.192 s
%------------------------------------------------------------------------------
