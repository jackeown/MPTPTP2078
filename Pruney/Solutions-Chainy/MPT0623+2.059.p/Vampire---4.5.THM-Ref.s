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
% DateTime   : Thu Dec  3 12:52:11 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 789 expanded)
%              Number of leaves         :    6 ( 192 expanded)
%              Depth                    :   24
%              Number of atoms          :  157 (2921 expanded)
%              Number of equality atoms :   56 (1078 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f653,plain,(
    $false ),
    inference(global_subsumption,[],[f570,f652])).

fof(f652,plain,(
    ! [X0] : sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f651,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f33,f35,f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f35,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f651,plain,(
    ! [X0] : sP3(X0,sK6(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f650,f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f650,plain,(
    ! [X0] : sP3(X0,sK6(k2_relat_1(k1_xboole_0),X0)) ),
    inference(forward_demodulation,[],[f620,f51])).

fof(f620,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(k1_xboole_0,X1)),X0)) ),
    inference(backward_demodulation,[],[f110,f619])).

fof(f619,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f573])).

fof(f573,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f17,f571])).

fof(f571,plain,(
    k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f229,f548])).

fof(f548,plain,(
    ! [X0] : k1_xboole_0 = k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f219,f536,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f536,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f516,f519])).

fof(f519,plain,(
    ! [X2,X1] :
      ( ~ sP3(X2,k1_funct_1(k1_xboole_0,X1))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f219,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f32,f51])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f516,plain,(
    ! [X2,X1] :
      ( sP3(X1,k1_funct_1(k1_xboole_0,X2))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f110,f98])).

fof(f219,plain,(
    ! [X0,X1] : ~ sP3(X0,sK6(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f170,f71])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK4(sK6(X1,X2),X3),X1)
      | ~ sP3(X3,sK6(X1,X2)) ) ),
    inference(superposition,[],[f23,f35])).

fof(f23,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f170,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f48,f168])).

fof(f168,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f121,f165])).

fof(f165,plain,(
    ! [X0,X1] : k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f123,f32])).

fof(f123,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f122,f35])).

fof(f122,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f112,f23])).

fof(f112,plain,(
    ! [X0] : sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f44,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] : r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f41,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f34,f33,f35,f16])).

fof(f16,plain,(
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

fof(f121,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f112,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f229,plain,(
    ! [X0] : sK0 = k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f170,f219,f27])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(sK1,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f44,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f100,f35])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f38,f32])).

fof(f38,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f570,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f550,f51])).

fof(f550,plain,(
    ! [X0,X1] : ~ sP3(X0,sK6(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f536,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (14152)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (14145)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (14160)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (14168)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (14151)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (14149)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (14149)Refutation not found, incomplete strategy% (14149)------------------------------
% 0.20/0.51  % (14149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14149)Memory used [KB]: 10618
% 0.20/0.51  % (14149)Time elapsed: 0.105 s
% 0.20/0.51  % (14149)------------------------------
% 0.20/0.51  % (14149)------------------------------
% 1.30/0.52  % (14164)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.52  % (14141)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.52  % (14153)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.52  % (14154)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.52  % (14162)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.53  % (14156)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.53  % (14144)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.53  % (14162)Refutation not found, incomplete strategy% (14162)------------------------------
% 1.30/0.53  % (14162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (14162)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (14162)Memory used [KB]: 10618
% 1.30/0.53  % (14162)Time elapsed: 0.087 s
% 1.30/0.53  % (14162)------------------------------
% 1.30/0.53  % (14162)------------------------------
% 1.30/0.53  % (14140)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (14140)Refutation not found, incomplete strategy% (14140)------------------------------
% 1.30/0.53  % (14140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (14140)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (14140)Memory used [KB]: 1663
% 1.30/0.53  % (14140)Time elapsed: 0.125 s
% 1.30/0.53  % (14140)------------------------------
% 1.30/0.53  % (14140)------------------------------
% 1.30/0.53  % (14143)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (14146)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (14142)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (14150)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  % (14142)Refutation not found, incomplete strategy% (14142)------------------------------
% 1.30/0.53  % (14142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (14142)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (14142)Memory used [KB]: 10618
% 1.30/0.53  % (14142)Time elapsed: 0.137 s
% 1.30/0.53  % (14142)------------------------------
% 1.30/0.53  % (14142)------------------------------
% 1.30/0.54  % (14150)Refutation not found, incomplete strategy% (14150)------------------------------
% 1.30/0.54  % (14150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (14150)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (14150)Memory used [KB]: 10618
% 1.30/0.54  % (14150)Time elapsed: 0.134 s
% 1.30/0.54  % (14150)------------------------------
% 1.30/0.54  % (14150)------------------------------
% 1.30/0.54  % (14165)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (14163)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.54  % (14169)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.54  % (14158)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.54  % (14147)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.54  % (14167)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.54  % (14157)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.54  % (14161)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.54  % (14157)Refutation not found, incomplete strategy% (14157)------------------------------
% 1.48/0.54  % (14157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.54  % (14166)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.54  % (14155)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.54  % (14159)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.54  % (14157)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.54  
% 1.48/0.54  % (14157)Memory used [KB]: 10618
% 1.48/0.54  % (14157)Time elapsed: 0.137 s
% 1.48/0.54  % (14157)------------------------------
% 1.48/0.54  % (14157)------------------------------
% 1.48/0.56  % (14148)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.56  % (14148)Refutation not found, incomplete strategy% (14148)------------------------------
% 1.48/0.56  % (14148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (14148)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (14148)Memory used [KB]: 10618
% 1.48/0.56  % (14148)Time elapsed: 0.158 s
% 1.48/0.56  % (14148)------------------------------
% 1.48/0.56  % (14148)------------------------------
% 1.48/0.57  % (14164)Refutation found. Thanks to Tanya!
% 1.48/0.57  % SZS status Theorem for theBenchmark
% 1.48/0.58  % SZS output start Proof for theBenchmark
% 1.48/0.58  fof(f653,plain,(
% 1.48/0.58    $false),
% 1.48/0.58    inference(global_subsumption,[],[f570,f652])).
% 1.48/0.58  fof(f652,plain,(
% 1.48/0.58    ( ! [X0] : (sP3(X0,k1_xboole_0)) )),
% 1.48/0.58    inference(forward_demodulation,[],[f651,f51])).
% 1.48/0.58  fof(f51,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.48/0.58    inference(unit_resulting_resolution,[],[f33,f35,f20])).
% 1.48/0.58  fof(f20,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,plain,(
% 1.48/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(flattening,[],[f10])).
% 1.48/0.58  fof(f10,plain,(
% 1.48/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.48/0.58  fof(f35,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f15])).
% 1.48/0.58  fof(f15,plain,(
% 1.48/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.48/0.58    inference(ennf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f15])).
% 1.48/0.58  fof(f651,plain,(
% 1.48/0.58    ( ! [X0] : (sP3(X0,sK6(k1_xboole_0,X0))) )),
% 1.48/0.58    inference(forward_demodulation,[],[f650,f19])).
% 1.48/0.58  fof(f19,plain,(
% 1.48/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.48/0.58    inference(cnf_transformation,[],[f2])).
% 1.48/0.59  fof(f2,axiom,(
% 1.48/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.48/0.59  fof(f650,plain,(
% 1.48/0.59    ( ! [X0] : (sP3(X0,sK6(k2_relat_1(k1_xboole_0),X0))) )),
% 1.48/0.59    inference(forward_demodulation,[],[f620,f51])).
% 1.48/0.59  fof(f620,plain,(
% 1.48/0.59    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(k1_xboole_0,X1)),X0))) )),
% 1.48/0.59    inference(backward_demodulation,[],[f110,f619])).
% 1.48/0.59  fof(f619,plain,(
% 1.48/0.59    k1_xboole_0 = sK1),
% 1.48/0.59    inference(trivial_inequality_removal,[],[f573])).
% 1.48/0.59  fof(f573,plain,(
% 1.48/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.48/0.59    inference(backward_demodulation,[],[f17,f571])).
% 1.48/0.59  fof(f571,plain,(
% 1.48/0.59    k1_xboole_0 = sK0),
% 1.48/0.59    inference(backward_demodulation,[],[f229,f548])).
% 1.48/0.59  fof(f548,plain,(
% 1.48/0.59    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X0))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f33,f34,f219,f536,f27])).
% 1.48/0.59  fof(f27,plain,(
% 1.48/0.59    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f13,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(flattening,[],[f12])).
% 1.48/0.59  fof(f12,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f4])).
% 1.48/0.59  fof(f4,axiom,(
% 1.48/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.48/0.59  fof(f536,plain,(
% 1.48/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.48/0.59    inference(global_subsumption,[],[f516,f519])).
% 1.48/0.59  fof(f519,plain,(
% 1.48/0.59    ( ! [X2,X1] : (~sP3(X2,k1_funct_1(k1_xboole_0,X1)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.48/0.59    inference(superposition,[],[f219,f98])).
% 1.48/0.59  fof(f98,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.48/0.59    inference(superposition,[],[f32,f51])).
% 1.48/0.59  fof(f32,plain,(
% 1.48/0.59    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f15])).
% 1.48/0.59  fof(f516,plain,(
% 1.48/0.59    ( ! [X2,X1] : (sP3(X1,k1_funct_1(k1_xboole_0,X2)) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.48/0.59    inference(superposition,[],[f110,f98])).
% 1.48/0.59  fof(f219,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~sP3(X0,sK6(sK0,X1))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f170,f71])).
% 1.48/0.59  fof(f71,plain,(
% 1.48/0.59    ( ! [X2,X3,X1] : (r2_hidden(sK4(sK6(X1,X2),X3),X1) | ~sP3(X3,sK6(X1,X2))) )),
% 1.48/0.59    inference(superposition,[],[f23,f35])).
% 1.48/0.59  fof(f23,plain,(
% 1.48/0.59    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f170,plain,(
% 1.48/0.59    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.48/0.59    inference(backward_demodulation,[],[f48,f168])).
% 1.48/0.59  fof(f168,plain,(
% 1.48/0.59    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 1.48/0.59    inference(backward_demodulation,[],[f121,f165])).
% 1.48/0.59  fof(f165,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f123,f32])).
% 1.48/0.59  fof(f123,plain,(
% 1.48/0.59    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f122,f35])).
% 1.48/0.59  fof(f122,plain,(
% 1.48/0.59    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0)))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f112,f23])).
% 1.48/0.59  fof(f112,plain,(
% 1.48/0.59    ( ! [X0] : (sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f33,f34,f44,f36])).
% 1.48/0.59  fof(f36,plain,(
% 1.48/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.48/0.59    inference(equality_resolution,[],[f26])).
% 1.48/0.59  fof(f26,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f44,plain,(
% 1.48/0.59    ( ! [X0] : (r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0)))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f41,f30])).
% 1.48/0.59  fof(f30,plain,(
% 1.48/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f14])).
% 1.48/0.59  fof(f14,plain,(
% 1.48/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f1])).
% 1.48/0.59  fof(f1,axiom,(
% 1.48/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.59  fof(f41,plain,(
% 1.48/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f34,f33,f35,f16])).
% 1.48/0.59  fof(f16,plain,(
% 1.48/0.59    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f9])).
% 1.48/0.59  fof(f9,plain,(
% 1.48/0.59    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.48/0.59    inference(flattening,[],[f8])).
% 1.48/0.59  fof(f8,plain,(
% 1.48/0.59    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f7])).
% 1.48/0.59  fof(f7,negated_conjecture,(
% 1.48/0.59    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.48/0.59    inference(negated_conjecture,[],[f6])).
% 1.48/0.59  fof(f6,conjecture,(
% 1.48/0.59    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.48/0.59  fof(f121,plain,(
% 1.48/0.59    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f112,f24])).
% 1.48/0.59  fof(f24,plain,(
% 1.48/0.59    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f48,plain,(
% 1.48/0.59    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0)) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f41,f31])).
% 1.48/0.59  fof(f31,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f14])).
% 1.48/0.59  fof(f34,plain,(
% 1.48/0.59    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f15])).
% 1.48/0.59  fof(f229,plain,(
% 1.48/0.59    ( ! [X0] : (sK0 = k2_relat_1(sK6(sK0,X0))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f33,f34,f170,f219,f27])).
% 1.48/0.59  fof(f17,plain,(
% 1.48/0.59    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.48/0.59    inference(cnf_transformation,[],[f9])).
% 1.48/0.59  fof(f110,plain,(
% 1.48/0.59    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(sK1,X1)),X0))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f44,f103])).
% 1.48/0.59  fof(f103,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f102])).
% 1.48/0.59  fof(f102,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f100,f35])).
% 1.48/0.59  fof(f100,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.48/0.59    inference(superposition,[],[f38,f32])).
% 1.48/0.59  fof(f38,plain,(
% 1.48/0.59    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.48/0.59    inference(equality_resolution,[],[f22])).
% 1.48/0.59  fof(f22,plain,(
% 1.48/0.59    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f570,plain,(
% 1.48/0.59    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f550,f51])).
% 1.48/0.59  fof(f550,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~sP3(X0,sK6(k1_xboole_0,X1))) )),
% 1.48/0.59    inference(unit_resulting_resolution,[],[f536,f71])).
% 1.48/0.59  % SZS output end Proof for theBenchmark
% 1.48/0.59  % (14164)------------------------------
% 1.48/0.59  % (14164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (14164)Termination reason: Refutation
% 1.48/0.59  
% 1.48/0.59  % (14164)Memory used [KB]: 6652
% 1.48/0.59  % (14164)Time elapsed: 0.163 s
% 1.48/0.59  % (14164)------------------------------
% 1.48/0.59  % (14164)------------------------------
% 1.48/0.59  % (14139)Success in time 0.238 s
%------------------------------------------------------------------------------
