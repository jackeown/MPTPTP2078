%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 677 expanded)
%              Number of leaves         :   11 ( 196 expanded)
%              Depth                    :   24
%              Number of atoms          :  242 (1726 expanded)
%              Number of equality atoms :  198 (1212 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(subsumption_resolution,[],[f377,f66])).

fof(f66,plain,(
    ! [X3] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X3) ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f29,f47])).

fof(f47,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,X0)) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(o_0_0_xboole_0,X1)) ),
    inference(resolution,[],[f59,f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f377,plain,(
    o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f376,f66])).

fof(f376,plain,(
    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f350,f66])).

fof(f350,plain,(
    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK2),sK3) ),
    inference(backward_demodulation,[],[f51,f349])).

fof(f349,plain,(
    o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f348,f66])).

fof(f348,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK3)
    | o_0_0_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f347,f66])).

fof(f347,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2),sK3)
    | o_0_0_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f339,f83])).

fof(f83,plain,(
    ! [X3] : o_0_0_xboole_0 = k2_zfmisc_1(X3,o_0_0_xboole_0) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,o_0_0_xboole_0)) ),
    inference(resolution,[],[f67,f31])).

fof(f67,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(X4,o_0_0_xboole_0)) ),
    inference(backward_demodulation,[],[f64,f66])).

% (4080)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f64,plain,(
    ! [X4,X5,X3] : ~ r2_hidden(X3,k2_zfmisc_1(X4,k2_zfmisc_1(o_0_0_xboole_0,X5))) ),
    inference(resolution,[],[f34,f60])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f339,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK2),sK3)
    | o_0_0_xboole_0 = sK0 ),
    inference(superposition,[],[f51,f338])).

fof(f338,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f194,f275,f308])).

fof(f308,plain,
    ( sK1 = sK5
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1 ),
    inference(equality_resolution,[],[f258])).

fof(f258,plain,(
    ! [X30,X31] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X30,X31)
      | o_0_0_xboole_0 = X30
      | sK5 = X31
      | o_0_0_xboole_0 = X31 ) ),
    inference(superposition,[],[f56,f238])).

fof(f238,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k2_zfmisc_1(sK4,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f166,f51])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k2_zfmisc_1(sK4,sK5) = X0
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(superposition,[],[f54,f141])).

fof(f141,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) ),
    inference(backward_demodulation,[],[f43,f138])).

fof(f138,plain,(
    sK3 = sK7 ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK7 = X2 ) ),
    inference(subsumption_resolution,[],[f106,f51])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK7 = X2
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(superposition,[],[f52,f43])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | X2 = X5
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(backward_demodulation,[],[f44,f47])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f40,f32,f32,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f17])).

% (4076)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f43,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f25,f41,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f25,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | X0 = X3
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(backward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f38,f32,f32,f32])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | o_0_0_xboole_0 = X0
      | X1 = X3
      | o_0_0_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f50,f47])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 = X0
      | X1 = X3
      | k1_xboole_0 = X1
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(backward_demodulation,[],[f37,f47])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f275,plain,
    ( sK0 = sK4
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1 ),
    inference(equality_resolution,[],[f256])).

fof(f256,plain,(
    ! [X26,X27] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X26,X27)
      | o_0_0_xboole_0 = X26
      | sK4 = X26
      | o_0_0_xboole_0 = X27 ) ),
    inference(superposition,[],[f55,f238])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | o_0_0_xboole_0 = X0
      | X0 = X2
      | o_0_0_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f49,f47])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 = X0
      | X0 = X2
      | k1_xboole_0 = X1
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(backward_demodulation,[],[f36,f47])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f194,plain,
    ( sK1 != sK5
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f193,f138])).

fof(f193,plain,
    ( sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( sK2 != sK2
    | sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f27,f182])).

fof(f182,plain,(
    sK2 = sK6 ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK6 = X1 ) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK6 = X1
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ) ),
    inference(superposition,[],[f53,f43])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | X1 = X4
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(backward_demodulation,[],[f45,f47])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f39,f32,f32,f32])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(backward_demodulation,[],[f42,f47])).

fof(f42,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (4078)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (4070)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (4062)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (4055)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (4060)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (4059)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (4077)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (4058)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (4057)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (4066)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (4067)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (4072)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (4075)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (4082)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (4083)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (4064)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (4069)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (4069)Refutation not found, incomplete strategy% (4069)------------------------------
% 0.21/0.56  % (4069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4069)Memory used [KB]: 1663
% 0.21/0.56  % (4069)Time elapsed: 0.150 s
% 0.21/0.56  % (4069)------------------------------
% 0.21/0.56  % (4069)------------------------------
% 0.21/0.57  % (4074)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.57  % (4084)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (4056)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.57  % (4061)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (4084)Refutation not found, incomplete strategy% (4084)------------------------------
% 0.21/0.57  % (4084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (4084)Memory used [KB]: 1663
% 0.21/0.57  % (4084)Time elapsed: 0.142 s
% 0.21/0.57  % (4084)------------------------------
% 0.21/0.57  % (4084)------------------------------
% 0.21/0.57  % (4079)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (4077)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f378,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f377,f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X3] : (o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X3)) )),
% 0.21/0.57    inference(resolution,[],[f61,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.57    inference(backward_demodulation,[],[f29,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k1_xboole_0),
% 0.21/0.57    inference(resolution,[],[f29,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,X0))) )),
% 0.21/0.57    inference(resolution,[],[f60,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(rectify,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(o_0_0_xboole_0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f59,f28])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.57    inference(resolution,[],[f33,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.57  fof(f377,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK3)),
% 0.21/0.57    inference(forward_demodulation,[],[f376,f66])).
% 0.21/0.57  fof(f376,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2),sK3)),
% 0.21/0.57    inference(forward_demodulation,[],[f350,f66])).
% 0.21/0.57  fof(f350,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK2),sK3)),
% 0.21/0.57    inference(backward_demodulation,[],[f51,f349])).
% 0.21/0.57  fof(f349,plain,(
% 0.21/0.57    o_0_0_xboole_0 = sK0),
% 0.21/0.57    inference(subsumption_resolution,[],[f348,f66])).
% 0.21/0.57  fof(f348,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK3) | o_0_0_xboole_0 = sK0),
% 0.21/0.57    inference(forward_demodulation,[],[f347,f66])).
% 0.21/0.57  fof(f347,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2),sK3) | o_0_0_xboole_0 = sK0),
% 0.21/0.57    inference(forward_demodulation,[],[f339,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X3] : (o_0_0_xboole_0 = k2_zfmisc_1(X3,o_0_0_xboole_0)) )),
% 0.21/0.57    inference(resolution,[],[f76,f48])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,o_0_0_xboole_0))) )),
% 0.21/0.57    inference(resolution,[],[f67,f31])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,o_0_0_xboole_0))) )),
% 0.21/0.57    inference(backward_demodulation,[],[f64,f66])).
% 0.21/0.57  % (4080)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,k2_zfmisc_1(o_0_0_xboole_0,X5)))) )),
% 0.21/0.57    inference(resolution,[],[f34,f60])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f339,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK2),sK3) | o_0_0_xboole_0 = sK0),
% 0.21/0.57    inference(superposition,[],[f51,f338])).
% 0.21/0.57  fof(f338,plain,(
% 0.21/0.57    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 0.21/0.57    inference(global_subsumption,[],[f194,f275,f308])).
% 0.21/0.57  fof(f308,plain,(
% 0.21/0.57    sK1 = sK5 | o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 = sK1),
% 0.21/0.57    inference(equality_resolution,[],[f258])).
% 0.21/0.57  fof(f258,plain,(
% 0.21/0.57    ( ! [X30,X31] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X30,X31) | o_0_0_xboole_0 = X30 | sK5 = X31 | o_0_0_xboole_0 = X31) )),
% 0.21/0.57    inference(superposition,[],[f56,f238])).
% 0.21/0.57  fof(f238,plain,(
% 0.21/0.57    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 0.21/0.57    inference(equality_resolution,[],[f174])).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f166,f51])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0 | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 0.21/0.57    inference(superposition,[],[f54,f141])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)),
% 0.21/0.57    inference(backward_demodulation,[],[f43,f138])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    sK3 = sK7),
% 0.21/0.57    inference(equality_resolution,[],[f114])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f106,f51])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2 | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 0.21/0.57    inference(superposition,[],[f52,f43])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | X2 = X5 | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f44,f47])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f40,f32,f32,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  % (4076)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.57    inference(definition_unfolding,[],[f25,f41,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f35,f32])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | X0 = X3 | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f46,f47])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f38,f32,f32,f32])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | o_0_0_xboole_0 = X0 | X1 = X3 | o_0_0_xboole_0 = X1) )),
% 0.21/0.57    inference(forward_demodulation,[],[f50,f47])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (o_0_0_xboole_0 = X0 | X1 = X3 | k1_xboole_0 = X1 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f37,f47])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (X1 = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    sK0 = sK4 | o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 = sK1),
% 0.21/0.57    inference(equality_resolution,[],[f256])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ( ! [X26,X27] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X26,X27) | o_0_0_xboole_0 = X26 | sK4 = X26 | o_0_0_xboole_0 = X27) )),
% 0.21/0.57    inference(superposition,[],[f55,f238])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | o_0_0_xboole_0 = X0 | X0 = X2 | o_0_0_xboole_0 = X1) )),
% 0.21/0.57    inference(forward_demodulation,[],[f49,f47])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (o_0_0_xboole_0 = X0 | X0 = X2 | k1_xboole_0 = X1 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f36,f47])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (X0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    sK1 != sK5 | sK0 != sK4),
% 0.21/0.57    inference(subsumption_resolution,[],[f193,f138])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f185])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    sK2 != sK2 | sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.57    inference(backward_demodulation,[],[f27,f182])).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    sK2 = sK6),
% 0.21/0.57    inference(equality_resolution,[],[f130])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1 | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) )),
% 0.21/0.57    inference(superposition,[],[f53,f43])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | X1 = X4 | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f45,f47])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f39,f32,f32,f32])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.57    inference(backward_demodulation,[],[f42,f47])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.57    inference(definition_unfolding,[],[f26,f41])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (4077)------------------------------
% 0.21/0.57  % (4077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4077)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (4077)Memory used [KB]: 6396
% 0.21/0.57  % (4077)Time elapsed: 0.162 s
% 0.21/0.57  % (4077)------------------------------
% 0.21/0.57  % (4077)------------------------------
% 0.21/0.57  % (4054)Success in time 0.202 s
%------------------------------------------------------------------------------
