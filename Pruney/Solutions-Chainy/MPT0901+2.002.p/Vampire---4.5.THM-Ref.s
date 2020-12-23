%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 254 expanded)
%              Number of leaves         :    8 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 (1607 expanded)
%              Number of equality atoms :  122 (1414 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44,f45])).

fof(f45,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f40,f43])).

fof(f43,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f21,f39])).

fof(f39,plain,(
    k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[],[f20,f34])).

fof(f34,plain,(
    k1_mcart_1(sK4) = k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[],[f20,f32])).

% (26712)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f32,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f31,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) )
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
              | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
              | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
              | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ( k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4)
            | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4)
            | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4)
            | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4) )
          & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X4] :
        ( ( k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4)
          | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4)
          | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4)
          | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4) )
        & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) )
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
            | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
            | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                  & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                  & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                  & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f31,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f30,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f28,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f19,f25,f22])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f20,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f35,f38])).

fof(f38,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f21,f34])).

fof(f35,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f18,f33])).

fof(f33,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(superposition,[],[f21,f32])).

fof(f18,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f20,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (26687)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (26702)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (26702)Refutation not found, incomplete strategy% (26702)------------------------------
% 0.21/0.55  % (26702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26702)Memory used [KB]: 6140
% 0.21/0.55  % (26702)Time elapsed: 0.003 s
% 0.21/0.55  % (26702)------------------------------
% 0.21/0.55  % (26702)------------------------------
% 0.21/0.57  % (26701)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (26691)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (26693)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (26691)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f44,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f40,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(superposition,[],[f21,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.57    inference(superposition,[],[f20,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    k1_mcart_1(sK4) = k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.57    inference(superposition,[],[f20,f32])).
% 0.21/0.57  % (26712)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f31,f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4) | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))) & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f11,f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X4] : ((k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4) | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X4] : ((k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4) | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4) | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))) & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.57    inference(negated_conjecture,[],[f6])).
% 0.21/0.57  fof(f6,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK0),
% 0.21/0.57    inference(subsumption_resolution,[],[f30,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.57    inference(subsumption_resolution,[],[f29,f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    k1_xboole_0 != sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.57    inference(subsumption_resolution,[],[f28,f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    k1_xboole_0 != sK3),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.57    inference(resolution,[],[f27,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    m1_subset_1(sK4,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.21/0.57    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f19,f25,f22])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f23,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f35,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(superposition,[],[f21,f34])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f18,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.21/0.57    inference(superposition,[],[f21,f32])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4) | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(superposition,[],[f20,f39])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (26691)------------------------------
% 0.21/0.57  % (26691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (26691)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (26691)Memory used [KB]: 6268
% 0.21/0.57  % (26691)Time elapsed: 0.138 s
% 0.21/0.57  % (26691)------------------------------
% 0.21/0.57  % (26691)------------------------------
% 0.21/0.57  % (26708)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (26686)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (26708)Refutation not found, incomplete strategy% (26708)------------------------------
% 0.21/0.57  % (26708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (26708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (26708)Memory used [KB]: 10746
% 0.21/0.57  % (26708)Time elapsed: 0.154 s
% 0.21/0.57  % (26708)------------------------------
% 0.21/0.57  % (26708)------------------------------
% 0.21/0.58  % (26710)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.58  % (26703)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (26692)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (26699)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (26711)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (26689)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (26711)Refutation not found, incomplete strategy% (26711)------------------------------
% 0.21/0.58  % (26711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (26711)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (26711)Memory used [KB]: 1663
% 0.21/0.58  % (26711)Time elapsed: 0.159 s
% 0.21/0.58  % (26711)------------------------------
% 0.21/0.58  % (26711)------------------------------
% 0.21/0.58  % (26709)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (26694)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (26714)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (26700)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (26706)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (26716)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.59  % (26717)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.59  % (26679)Success in time 0.225 s
%------------------------------------------------------------------------------
