%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0533+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   32 (  68 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4158,f1812])).

fof(f1812,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f1392])).

% (16442)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
fof(f1392,plain,
    ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6))
    & r1_tarski(sK3,sK4)
    & r1_tarski(sK5,sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f798,f1391,f1390])).

fof(f1390,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,X3))
          & r1_tarski(sK3,sK4)
          & r1_tarski(sK5,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1391,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,X3))
        & r1_tarski(sK3,sK4)
        & r1_tarski(sK5,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6))
      & r1_tarski(sK3,sK4)
      & r1_tarski(sK5,sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f798,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f797])).

fof(f797,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f710])).

fof(f710,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f709])).

fof(f709,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f4158,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4157,f1809])).

fof(f1809,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1392])).

fof(f4157,plain,
    ( ~ v1_relat_1(sK5)
    | ~ r1_tarski(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4156,f1810])).

fof(f1810,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f1392])).

fof(f4156,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ r1_tarski(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4154,f1811])).

fof(f1811,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f1392])).

fof(f4154,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ r1_tarski(sK3,sK4) ),
    inference(resolution,[],[f2145,f4150])).

fof(f4150,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(X0,sK5),k8_relat_1(sK4,sK6))
      | ~ r1_tarski(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f4149,f1809])).

fof(f4149,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | ~ v1_relat_1(sK5)
      | ~ r1_tarski(k8_relat_1(X0,sK5),k8_relat_1(sK4,sK6)) ) ),
    inference(resolution,[],[f2514,f4137])).

fof(f4137,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(sK3,sK5),X0)
      | ~ r1_tarski(X0,k8_relat_1(sK4,sK6)) ) ),
    inference(resolution,[],[f2595,f1813])).

fof(f1813,plain,(
    ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f1392])).

fof(f2595,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1273])).

% (16454)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f1273,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1272])).

fof(f1272,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2514,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1176])).

fof(f1176,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1175])).

fof(f1175,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f707,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

fof(f2145,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f955])).

fof(f955,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f954])).

fof(f954,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f708,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
%------------------------------------------------------------------------------
