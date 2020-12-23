%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0452+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 121 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 245 expanded)
%              Number of equality atoms :   35 ( 117 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2750,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2749,f1099])).

fof(f1099,plain,(
    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f916])).

fof(f916,plain,
    ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f682,f915])).

fof(f915,plain,
    ( ? [X0] :
        ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f682,plain,(
    ? [X0] :
      ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f677])).

fof(f677,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f676])).

fof(f676,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).

fof(f2749,plain,(
    k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2748,f2686])).

fof(f2686,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f2674,f2685])).

fof(f2685,plain,(
    k3_relat_1(sK0) = k2_relat_1(k2_xboole_0(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f2684,f1884])).

fof(f1884,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1098,f1114])).

fof(f1114,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f693])).

fof(f693,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f1098,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f916])).

fof(f2684,plain,(
    k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f2683,f1504])).

fof(f1504,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2683,plain,(
    k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f2544,f1869])).

fof(f1869,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1098,f1105])).

fof(f1105,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f684])).

fof(f684,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f675])).

fof(f675,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f2544,plain,(
    k2_relat_1(k2_xboole_0(k4_relat_1(sK0),sK0)) = k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1098,f1871,f1327])).

fof(f1327,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f783])).

fof(f783,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f1871,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1098,f1107])).

fof(f1107,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f686])).

fof(f686,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f648])).

% (18949)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
fof(f648,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f2674,plain,(
    k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f2550,f1869])).

fof(f2550,plain,(
    k2_relat_1(k2_xboole_0(sK0,k4_relat_1(sK0))) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f1098,f1871,f1327])).

fof(f2748,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2747,f1868])).

fof(f1868,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1098,f1104])).

fof(f1104,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f684])).

fof(f2747,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2475,f1869])).

fof(f2475,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f1871,f1114])).
%------------------------------------------------------------------------------
