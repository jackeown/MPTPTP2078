%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:52 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 351 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 (1308 expanded)
%              Number of equality atoms :   47 ( 457 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f119,f120])).

fof(f120,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f118,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f118,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(resolution,[],[f114,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f56,f37])).

fof(f37,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f35,f22])).

fof(f35,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) ) ),
    inference(superposition,[],[f26,f42])).

fof(f42,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f41,f22])).

fof(f41,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f39,f23])).

fof(f39,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f114,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f47,f42])).

fof(f47,plain,(
    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f43,f22])).

fof(f43,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f40,f23])).

fof(f40,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK0),X0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f46,f42])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK0),X0),k1_relat_1(k2_funct_1(sK0))) ),
    inference(resolution,[],[f37,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f119,plain,(
    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f117,f22])).

fof(f117,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f59,f44])).

fof(f59,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) ) ),
    inference(superposition,[],[f25,f42])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f21,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:49:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (803766272)
% 0.14/0.37  ipcrm: permission denied for id (803799041)
% 0.14/0.37  ipcrm: permission denied for id (803831811)
% 0.14/0.38  ipcrm: permission denied for id (806617093)
% 0.14/0.38  ipcrm: permission denied for id (803897351)
% 0.14/0.38  ipcrm: permission denied for id (803930120)
% 0.14/0.38  ipcrm: permission denied for id (803962889)
% 0.14/0.38  ipcrm: permission denied for id (804028428)
% 0.14/0.39  ipcrm: permission denied for id (806780942)
% 0.14/0.39  ipcrm: permission denied for id (804126738)
% 0.14/0.39  ipcrm: permission denied for id (804159507)
% 0.14/0.39  ipcrm: permission denied for id (806912020)
% 0.14/0.40  ipcrm: permission denied for id (804192277)
% 0.14/0.40  ipcrm: permission denied for id (807010328)
% 0.14/0.40  ipcrm: permission denied for id (807043097)
% 0.22/0.40  ipcrm: permission denied for id (804290587)
% 0.22/0.40  ipcrm: permission denied for id (804323356)
% 0.22/0.41  ipcrm: permission denied for id (804421663)
% 0.22/0.41  ipcrm: permission denied for id (807206944)
% 0.22/0.41  ipcrm: permission denied for id (807239713)
% 0.22/0.41  ipcrm: permission denied for id (807272482)
% 0.22/0.41  ipcrm: permission denied for id (804519972)
% 0.22/0.41  ipcrm: permission denied for id (804552741)
% 0.22/0.42  ipcrm: permission denied for id (804585510)
% 0.22/0.42  ipcrm: permission denied for id (807338023)
% 0.22/0.42  ipcrm: permission denied for id (804651048)
% 0.22/0.42  ipcrm: permission denied for id (804683817)
% 0.22/0.42  ipcrm: permission denied for id (807370794)
% 0.22/0.42  ipcrm: permission denied for id (807403563)
% 0.22/0.42  ipcrm: permission denied for id (804814892)
% 0.22/0.43  ipcrm: permission denied for id (807469102)
% 0.22/0.43  ipcrm: permission denied for id (804782127)
% 0.22/0.43  ipcrm: permission denied for id (804880433)
% 0.22/0.43  ipcrm: permission denied for id (804913202)
% 0.22/0.44  ipcrm: permission denied for id (807567412)
% 0.22/0.44  ipcrm: permission denied for id (804945974)
% 0.22/0.44  ipcrm: permission denied for id (807632951)
% 0.22/0.44  ipcrm: permission denied for id (807665720)
% 0.22/0.44  ipcrm: permission denied for id (805011513)
% 0.22/0.45  ipcrm: permission denied for id (805044282)
% 0.22/0.45  ipcrm: permission denied for id (805077051)
% 0.22/0.45  ipcrm: permission denied for id (805109821)
% 0.22/0.45  ipcrm: permission denied for id (807796799)
% 0.22/0.46  ipcrm: permission denied for id (807862337)
% 0.22/0.46  ipcrm: permission denied for id (807960644)
% 0.22/0.46  ipcrm: permission denied for id (807993413)
% 0.22/0.46  ipcrm: permission denied for id (808026182)
% 0.22/0.47  ipcrm: permission denied for id (808058951)
% 0.22/0.47  ipcrm: permission denied for id (808091720)
% 0.22/0.47  ipcrm: permission denied for id (808157258)
% 0.22/0.47  ipcrm: permission denied for id (808190027)
% 0.22/0.47  ipcrm: permission denied for id (805437516)
% 0.22/0.48  ipcrm: permission denied for id (805535825)
% 0.22/0.48  ipcrm: permission denied for id (808353874)
% 0.22/0.48  ipcrm: permission denied for id (808386643)
% 0.22/0.48  ipcrm: permission denied for id (805601364)
% 0.22/0.49  ipcrm: permission denied for id (805634134)
% 0.22/0.49  ipcrm: permission denied for id (805666903)
% 0.22/0.49  ipcrm: permission denied for id (805732441)
% 0.22/0.49  ipcrm: permission denied for id (808517723)
% 0.22/0.50  ipcrm: permission denied for id (808583261)
% 0.22/0.50  ipcrm: permission denied for id (808616030)
% 0.22/0.50  ipcrm: permission denied for id (805830752)
% 0.22/0.50  ipcrm: permission denied for id (808681569)
% 0.22/0.51  ipcrm: permission denied for id (808714338)
% 0.22/0.51  ipcrm: permission denied for id (805929059)
% 0.22/0.51  ipcrm: permission denied for id (808812646)
% 0.22/0.51  ipcrm: permission denied for id (808845415)
% 0.22/0.52  ipcrm: permission denied for id (808910953)
% 0.22/0.52  ipcrm: permission denied for id (806027370)
% 0.22/0.52  ipcrm: permission denied for id (808976492)
% 0.22/0.52  ipcrm: permission denied for id (806125678)
% 0.22/0.52  ipcrm: permission denied for id (806158447)
% 0.22/0.53  ipcrm: permission denied for id (809042032)
% 0.22/0.53  ipcrm: permission denied for id (809107570)
% 0.22/0.53  ipcrm: permission denied for id (809173108)
% 0.22/0.53  ipcrm: permission denied for id (806256757)
% 0.22/0.54  ipcrm: permission denied for id (809304185)
% 0.22/0.54  ipcrm: permission denied for id (809336954)
% 0.22/0.54  ipcrm: permission denied for id (806453372)
% 0.22/0.55  ipcrm: permission denied for id (806518910)
% 0.22/0.55  ipcrm: permission denied for id (809435263)
% 0.78/0.63  % (5117)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.78/0.64  % (5125)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.78/0.64  % (5110)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.78/0.66  % (5129)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.78/0.66  % (5129)Refutation found. Thanks to Tanya!
% 0.78/0.66  % SZS status Theorem for theBenchmark
% 0.78/0.66  % SZS output start Proof for theBenchmark
% 0.78/0.66  fof(f121,plain,(
% 0.78/0.66    $false),
% 0.78/0.66    inference(global_subsumption,[],[f21,f119,f120])).
% 0.78/0.66  fof(f120,plain,(
% 0.78/0.66    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.78/0.66    inference(subsumption_resolution,[],[f118,f22])).
% 0.78/0.66  fof(f22,plain,(
% 0.78/0.66    v1_relat_1(sK0)),
% 0.78/0.66    inference(cnf_transformation,[],[f10])).
% 0.78/0.66  fof(f10,plain,(
% 0.78/0.66    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.78/0.66    inference(flattening,[],[f9])).
% 0.78/0.66  fof(f9,plain,(
% 0.78/0.66    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.78/0.66    inference(ennf_transformation,[],[f8])).
% 0.78/0.66  fof(f8,negated_conjecture,(
% 0.78/0.66    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.78/0.66    inference(negated_conjecture,[],[f7])).
% 0.78/0.66  fof(f7,conjecture,(
% 0.78/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.78/0.66  fof(f118,plain,(
% 0.78/0.66    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.78/0.66    inference(resolution,[],[f114,f58])).
% 0.78/0.66  fof(f58,plain,(
% 0.78/0.66    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))) )),
% 0.78/0.66    inference(subsumption_resolution,[],[f56,f37])).
% 0.78/0.66  fof(f37,plain,(
% 0.78/0.66    v1_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(subsumption_resolution,[],[f35,f22])).
% 0.78/0.66  fof(f35,plain,(
% 0.78/0.66    ~v1_relat_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(resolution,[],[f23,f29])).
% 0.78/0.66  fof(f29,plain,(
% 0.78/0.66    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.78/0.66    inference(cnf_transformation,[],[f18])).
% 0.78/0.66  fof(f18,plain,(
% 0.78/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(flattening,[],[f17])).
% 0.78/0.66  fof(f17,plain,(
% 0.78/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.78/0.66    inference(ennf_transformation,[],[f5])).
% 0.78/0.66  fof(f5,axiom,(
% 0.78/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.78/0.66  fof(f23,plain,(
% 0.78/0.66    v1_funct_1(sK0)),
% 0.78/0.66    inference(cnf_transformation,[],[f10])).
% 0.78/0.66  fof(f56,plain,(
% 0.78/0.66    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))) )),
% 0.78/0.66    inference(superposition,[],[f26,f42])).
% 0.78/0.66  fof(f42,plain,(
% 0.78/0.66    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(subsumption_resolution,[],[f41,f22])).
% 0.78/0.66  fof(f41,plain,(
% 0.78/0.66    ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(subsumption_resolution,[],[f39,f23])).
% 0.78/0.66  fof(f39,plain,(
% 0.78/0.66    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(resolution,[],[f24,f27])).
% 0.78/0.66  fof(f27,plain,(
% 0.78/0.66    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.78/0.66    inference(cnf_transformation,[],[f16])).
% 0.78/0.66  fof(f16,plain,(
% 0.78/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(flattening,[],[f15])).
% 0.78/0.66  fof(f15,plain,(
% 0.78/0.66    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.78/0.66    inference(ennf_transformation,[],[f6])).
% 0.78/0.66  fof(f6,axiom,(
% 0.78/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.78/0.66  fof(f24,plain,(
% 0.78/0.66    v2_funct_1(sK0)),
% 0.78/0.66    inference(cnf_transformation,[],[f10])).
% 0.78/0.66  fof(f26,plain,(
% 0.78/0.66    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.78/0.66    inference(cnf_transformation,[],[f14])).
% 0.78/0.66  fof(f14,plain,(
% 0.78/0.66    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(flattening,[],[f13])).
% 0.78/0.66  fof(f13,plain,(
% 0.78/0.66    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(ennf_transformation,[],[f3])).
% 0.78/0.66  fof(f3,axiom,(
% 0.78/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.78/0.66  fof(f114,plain,(
% 0.78/0.66    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.78/0.66    inference(superposition,[],[f49,f48])).
% 0.78/0.66  fof(f48,plain,(
% 0.78/0.66    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 0.78/0.66    inference(forward_demodulation,[],[f47,f42])).
% 0.78/0.66  fof(f47,plain,(
% 0.78/0.66    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 0.78/0.66    inference(forward_demodulation,[],[f45,f44])).
% 0.78/0.66  fof(f44,plain,(
% 0.78/0.66    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(subsumption_resolution,[],[f43,f22])).
% 0.78/0.66  fof(f43,plain,(
% 0.78/0.66    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(subsumption_resolution,[],[f40,f23])).
% 0.78/0.66  fof(f40,plain,(
% 0.78/0.66    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.78/0.66    inference(resolution,[],[f24,f28])).
% 0.78/0.66  fof(f28,plain,(
% 0.78/0.66    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.78/0.66    inference(cnf_transformation,[],[f16])).
% 0.78/0.66  fof(f45,plain,(
% 0.78/0.66    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))),
% 0.78/0.66    inference(resolution,[],[f37,f32])).
% 0.78/0.66  fof(f32,plain,(
% 0.78/0.66    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.78/0.66    inference(cnf_transformation,[],[f20])).
% 0.78/0.66  fof(f20,plain,(
% 0.78/0.66    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(ennf_transformation,[],[f2])).
% 0.78/0.66  fof(f2,axiom,(
% 0.78/0.66    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.78/0.66  fof(f49,plain,(
% 0.78/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK0),X0),k2_relat_1(sK0))) )),
% 0.78/0.66    inference(forward_demodulation,[],[f46,f42])).
% 0.78/0.66  fof(f46,plain,(
% 0.78/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK0),X0),k1_relat_1(k2_funct_1(sK0)))) )),
% 0.78/0.66    inference(resolution,[],[f37,f31])).
% 0.78/0.66  fof(f31,plain,(
% 0.78/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.78/0.66    inference(cnf_transformation,[],[f19])).
% 0.78/0.66  fof(f19,plain,(
% 0.78/0.66    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.78/0.66    inference(ennf_transformation,[],[f1])).
% 0.78/0.66  fof(f1,axiom,(
% 0.78/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.78/0.66  fof(f119,plain,(
% 0.78/0.66    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.78/0.66    inference(subsumption_resolution,[],[f117,f22])).
% 0.78/0.66  fof(f117,plain,(
% 0.78/0.66    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_relat_1(sK0)),
% 0.78/0.66    inference(resolution,[],[f114,f60])).
% 0.78/0.66  fof(f60,plain,(
% 0.78/0.66    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) | ~v1_relat_1(X1)) )),
% 0.78/0.66    inference(forward_demodulation,[],[f59,f44])).
% 0.78/0.66  fof(f59,plain,(
% 0.78/0.66    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | ~v1_relat_1(X1) | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))) )),
% 0.78/0.66    inference(subsumption_resolution,[],[f57,f37])).
% 0.78/0.66  fof(f57,plain,(
% 0.78/0.66    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(sK0)) | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))) )),
% 0.78/0.66    inference(superposition,[],[f25,f42])).
% 0.78/0.66  fof(f25,plain,(
% 0.78/0.66    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.78/0.66    inference(cnf_transformation,[],[f12])).
% 0.78/0.66  fof(f12,plain,(
% 0.78/0.66    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(flattening,[],[f11])).
% 0.78/0.66  fof(f11,plain,(
% 0.78/0.66    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.78/0.66    inference(ennf_transformation,[],[f4])).
% 0.78/0.66  fof(f4,axiom,(
% 0.78/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.78/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.78/0.66  fof(f21,plain,(
% 0.78/0.66    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.78/0.66    inference(cnf_transformation,[],[f10])).
% 0.78/0.66  % SZS output end Proof for theBenchmark
% 0.78/0.66  % (5129)------------------------------
% 0.78/0.66  % (5129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.78/0.66  % (5129)Termination reason: Refutation
% 0.78/0.66  
% 0.78/0.66  % (5129)Memory used [KB]: 6140
% 0.78/0.66  % (5129)Time elapsed: 0.067 s
% 0.78/0.66  % (5129)------------------------------
% 0.78/0.66  % (5129)------------------------------
% 0.78/0.66  % (5115)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.78/0.67  % (5113)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.78/0.68  % (4945)Success in time 0.309 s
%------------------------------------------------------------------------------
