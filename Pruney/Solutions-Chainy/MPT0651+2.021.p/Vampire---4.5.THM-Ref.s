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
% DateTime   : Thu Dec  3 12:52:51 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 239 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 ( 963 expanded)
%              Number of equality atoms :   63 ( 372 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f233])).

fof(f233,plain,(
    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f229,f41])).

fof(f41,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f229,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f70,f47])).

fof(f47,plain,(
    ! [X2] :
      ( k2_relat_1(k5_relat_1(sK0,X2)) = k9_relat_1(X2,k2_relat_1(sK0))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f70,plain,(
    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f69,f44])).

fof(f44,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f69,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f59,f43])).

fof(f43,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f324,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f323])).

fof(f323,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f55,f322])).

fof(f322,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f175,f242])).

fof(f242,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f235,f41])).

fof(f235,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f46,f162])).

fof(f162,plain,(
    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f161,f42])).

fof(f42,plain,(
    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(resolution,[],[f25,f34])).

fof(f161,plain,(
    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f155,f44])).

fof(f155,plain,(
    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k2_relat_1(k5_relat_1(X3,sK0)) = k9_relat_1(sK0,k2_relat_1(X3)) ) ),
    inference(resolution,[],[f25,f38])).

fof(f46,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,sK0)),k2_relat_1(sK0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f175,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f171,f41])).

fof(f171,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f49,f43])).

fof(f49,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(X4))
      | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f25,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f55,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f25,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f54,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(backward_demodulation,[],[f28,f53])).

fof(f28,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (812941314)
% 0.21/0.37  ipcrm: permission denied for id (813039622)
% 0.21/0.37  ipcrm: permission denied for id (813072391)
% 0.21/0.37  ipcrm: permission denied for id (816611336)
% 0.21/0.38  ipcrm: permission denied for id (813137930)
% 0.21/0.38  ipcrm: permission denied for id (813203469)
% 0.21/0.38  ipcrm: permission denied for id (816742414)
% 0.21/0.38  ipcrm: permission denied for id (816807952)
% 0.21/0.39  ipcrm: permission denied for id (813301777)
% 0.21/0.39  ipcrm: permission denied for id (816906260)
% 0.21/0.39  ipcrm: permission denied for id (816939029)
% 0.21/0.39  ipcrm: permission denied for id (817004567)
% 0.21/0.40  ipcrm: permission denied for id (817102874)
% 0.21/0.40  ipcrm: permission denied for id (813596699)
% 0.21/0.40  ipcrm: permission denied for id (813629468)
% 0.21/0.40  ipcrm: permission denied for id (813695006)
% 0.21/0.40  ipcrm: permission denied for id (817168415)
% 0.21/0.40  ipcrm: permission denied for id (817201184)
% 0.21/0.40  ipcrm: permission denied for id (817233953)
% 0.21/0.40  ipcrm: permission denied for id (817266722)
% 0.21/0.41  ipcrm: permission denied for id (813858852)
% 0.21/0.41  ipcrm: permission denied for id (817332261)
% 0.21/0.41  ipcrm: permission denied for id (813924391)
% 0.21/0.41  ipcrm: permission denied for id (817397800)
% 0.21/0.41  ipcrm: permission denied for id (817430569)
% 0.21/0.41  ipcrm: permission denied for id (817463338)
% 0.21/0.42  ipcrm: permission denied for id (817496107)
% 0.21/0.42  ipcrm: permission denied for id (817561645)
% 0.21/0.42  ipcrm: permission denied for id (814088238)
% 0.21/0.42  ipcrm: permission denied for id (817627184)
% 0.21/0.42  ipcrm: permission denied for id (814153777)
% 0.21/0.43  ipcrm: permission denied for id (814186547)
% 0.21/0.43  ipcrm: permission denied for id (814252084)
% 0.21/0.43  ipcrm: permission denied for id (814284853)
% 0.21/0.43  ipcrm: permission denied for id (817758264)
% 0.21/0.43  ipcrm: permission denied for id (817856571)
% 0.21/0.44  ipcrm: permission denied for id (814481468)
% 0.21/0.44  ipcrm: permission denied for id (817889341)
% 0.21/0.44  ipcrm: permission denied for id (814547006)
% 0.21/0.44  ipcrm: permission denied for id (814678080)
% 0.21/0.44  ipcrm: permission denied for id (818020418)
% 0.21/0.44  ipcrm: permission denied for id (814743619)
% 0.21/0.45  ipcrm: permission denied for id (818053188)
% 0.21/0.45  ipcrm: permission denied for id (818085957)
% 0.21/0.45  ipcrm: permission denied for id (818118726)
% 0.21/0.45  ipcrm: permission denied for id (814841927)
% 0.21/0.45  ipcrm: permission denied for id (814874697)
% 0.21/0.45  ipcrm: permission denied for id (814907466)
% 0.21/0.45  ipcrm: permission denied for id (818184267)
% 0.21/0.45  ipcrm: permission denied for id (818217036)
% 0.21/0.46  ipcrm: permission denied for id (815104079)
% 0.21/0.46  ipcrm: permission denied for id (815136848)
% 0.21/0.46  ipcrm: permission denied for id (818315345)
% 0.21/0.46  ipcrm: permission denied for id (815169618)
% 0.21/0.46  ipcrm: permission denied for id (815202387)
% 0.21/0.46  ipcrm: permission denied for id (815235156)
% 0.21/0.47  ipcrm: permission denied for id (815267925)
% 0.21/0.47  ipcrm: permission denied for id (815300694)
% 0.21/0.47  ipcrm: permission denied for id (815333463)
% 0.21/0.47  ipcrm: permission denied for id (818413658)
% 0.21/0.47  ipcrm: permission denied for id (815464539)
% 0.21/0.47  ipcrm: permission denied for id (818446428)
% 0.21/0.48  ipcrm: permission denied for id (818511966)
% 0.21/0.48  ipcrm: permission denied for id (815497311)
% 0.21/0.48  ipcrm: permission denied for id (815530080)
% 0.21/0.48  ipcrm: permission denied for id (815562849)
% 0.21/0.48  ipcrm: permission denied for id (818577506)
% 0.21/0.48  ipcrm: permission denied for id (815661156)
% 0.21/0.48  ipcrm: permission denied for id (818643045)
% 0.21/0.49  ipcrm: permission denied for id (815726694)
% 0.21/0.49  ipcrm: permission denied for id (818675815)
% 0.21/0.49  ipcrm: permission denied for id (815792232)
% 0.21/0.49  ipcrm: permission denied for id (818708585)
% 0.21/0.49  ipcrm: permission denied for id (815857770)
% 0.21/0.49  ipcrm: permission denied for id (815890539)
% 0.21/0.49  ipcrm: permission denied for id (818741356)
% 0.21/0.49  ipcrm: permission denied for id (818774125)
% 0.21/0.50  ipcrm: permission denied for id (818839663)
% 0.21/0.50  ipcrm: permission denied for id (818905201)
% 0.21/0.50  ipcrm: permission denied for id (816054386)
% 0.21/0.50  ipcrm: permission denied for id (818937971)
% 0.21/0.50  ipcrm: permission denied for id (816119924)
% 0.21/0.51  ipcrm: permission denied for id (816185463)
% 0.21/0.51  ipcrm: permission denied for id (819036280)
% 0.21/0.51  ipcrm: permission denied for id (816316539)
% 0.21/0.51  ipcrm: permission denied for id (819134588)
% 0.21/0.51  ipcrm: permission denied for id (816349309)
% 0.21/0.51  ipcrm: permission denied for id (819167358)
% 0.21/0.52  ipcrm: permission denied for id (816414847)
% 0.51/0.62  % (26837)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.07/0.63  % (26837)Refutation not found, incomplete strategy% (26837)------------------------------
% 1.07/0.63  % (26837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.07/0.63  % (26837)Termination reason: Refutation not found, incomplete strategy
% 1.07/0.63  
% 1.07/0.63  % (26837)Memory used [KB]: 10618
% 1.07/0.63  % (26837)Time elapsed: 0.069 s
% 1.07/0.63  % (26837)------------------------------
% 1.07/0.63  % (26837)------------------------------
% 1.07/0.63  % (26844)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.07/0.63  % (26850)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.07/0.63  % (26845)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.07/0.64  % (26851)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.07/0.64  % (26835)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.07/0.64  % (26845)Refutation found. Thanks to Tanya!
% 1.07/0.64  % SZS status Theorem for theBenchmark
% 1.07/0.64  % SZS output start Proof for theBenchmark
% 1.07/0.64  fof(f325,plain,(
% 1.07/0.64    $false),
% 1.07/0.64    inference(subsumption_resolution,[],[f324,f233])).
% 1.07/0.64  fof(f233,plain,(
% 1.07/0.64    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 1.07/0.64    inference(subsumption_resolution,[],[f229,f41])).
% 1.07/0.64  fof(f41,plain,(
% 1.07/0.64    v1_relat_1(k4_relat_1(sK0))),
% 1.07/0.64    inference(resolution,[],[f25,f33])).
% 1.07/0.64  fof(f33,plain,(
% 1.07/0.64    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f14])).
% 1.07/0.64  fof(f14,plain,(
% 1.07/0.64    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(ennf_transformation,[],[f1])).
% 1.07/0.64  fof(f1,axiom,(
% 1.07/0.64    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.07/0.64  fof(f25,plain,(
% 1.07/0.64    v1_relat_1(sK0)),
% 1.07/0.64    inference(cnf_transformation,[],[f24])).
% 1.07/0.64  fof(f24,plain,(
% 1.07/0.64    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.07/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).
% 1.07/0.64  fof(f23,plain,(
% 1.07/0.64    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.07/0.64    introduced(choice_axiom,[])).
% 1.07/0.64  fof(f13,plain,(
% 1.07/0.64    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.07/0.64    inference(flattening,[],[f12])).
% 1.07/0.64  fof(f12,plain,(
% 1.07/0.64    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.07/0.64    inference(ennf_transformation,[],[f11])).
% 1.07/0.64  fof(f11,negated_conjecture,(
% 1.07/0.64    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.07/0.64    inference(negated_conjecture,[],[f10])).
% 1.07/0.64  fof(f10,conjecture,(
% 1.07/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.07/0.64  fof(f229,plain,(
% 1.07/0.64    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 1.07/0.64    inference(superposition,[],[f70,f47])).
% 1.07/0.64  fof(f47,plain,(
% 1.07/0.64    ( ! [X2] : (k2_relat_1(k5_relat_1(sK0,X2)) = k9_relat_1(X2,k2_relat_1(sK0)) | ~v1_relat_1(X2)) )),
% 1.07/0.64    inference(resolution,[],[f25,f38])).
% 1.07/0.64  fof(f38,plain,(
% 1.07/0.64    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f18])).
% 1.07/0.64  fof(f18,plain,(
% 1.07/0.64    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(ennf_transformation,[],[f3])).
% 1.07/0.64  fof(f3,axiom,(
% 1.07/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.07/0.64  fof(f70,plain,(
% 1.07/0.64    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 1.07/0.64    inference(forward_demodulation,[],[f69,f44])).
% 1.07/0.64  fof(f44,plain,(
% 1.07/0.64    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 1.07/0.64    inference(resolution,[],[f25,f36])).
% 1.07/0.64  fof(f36,plain,(
% 1.07/0.64    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f16])).
% 1.07/0.64  fof(f16,plain,(
% 1.07/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(ennf_transformation,[],[f4])).
% 1.07/0.64  fof(f4,axiom,(
% 1.07/0.64    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.07/0.64  fof(f69,plain,(
% 1.07/0.64    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 1.07/0.64    inference(forward_demodulation,[],[f59,f43])).
% 1.07/0.64  fof(f43,plain,(
% 1.07/0.64    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 1.07/0.64    inference(resolution,[],[f25,f35])).
% 1.07/0.64  fof(f35,plain,(
% 1.07/0.64    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f16])).
% 1.07/0.64  fof(f59,plain,(
% 1.07/0.64    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 1.07/0.64    inference(resolution,[],[f41,f34])).
% 1.07/0.64  fof(f34,plain,(
% 1.07/0.64    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f15])).
% 1.07/0.64  fof(f15,plain,(
% 1.07/0.64    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(ennf_transformation,[],[f2])).
% 1.07/0.64  fof(f2,axiom,(
% 1.07/0.64    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.07/0.64  fof(f324,plain,(
% 1.07/0.64    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 1.07/0.64    inference(trivial_inequality_removal,[],[f323])).
% 1.07/0.64  fof(f323,plain,(
% 1.07/0.64    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 1.07/0.64    inference(backward_demodulation,[],[f55,f322])).
% 1.07/0.64  fof(f322,plain,(
% 1.07/0.64    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 1.07/0.64    inference(resolution,[],[f175,f242])).
% 1.07/0.64  fof(f242,plain,(
% 1.07/0.64    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 1.07/0.64    inference(subsumption_resolution,[],[f235,f41])).
% 1.07/0.64  fof(f235,plain,(
% 1.07/0.64    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 1.07/0.64    inference(superposition,[],[f46,f162])).
% 1.07/0.64  fof(f162,plain,(
% 1.07/0.64    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 1.07/0.64    inference(forward_demodulation,[],[f161,f42])).
% 1.07/0.64  fof(f42,plain,(
% 1.07/0.64    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0)),
% 1.07/0.64    inference(resolution,[],[f25,f34])).
% 1.07/0.64  fof(f161,plain,(
% 1.07/0.64    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 1.07/0.64    inference(forward_demodulation,[],[f155,f44])).
% 1.07/0.64  fof(f155,plain,(
% 1.07/0.64    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0)))),
% 1.07/0.64    inference(resolution,[],[f48,f41])).
% 1.07/0.64  fof(f48,plain,(
% 1.07/0.64    ( ! [X3] : (~v1_relat_1(X3) | k2_relat_1(k5_relat_1(X3,sK0)) = k9_relat_1(sK0,k2_relat_1(X3))) )),
% 1.07/0.64    inference(resolution,[],[f25,f38])).
% 1.07/0.64  fof(f46,plain,(
% 1.07/0.64    ( ! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,sK0)),k2_relat_1(sK0)) | ~v1_relat_1(X1)) )),
% 1.07/0.64    inference(resolution,[],[f25,f37])).
% 1.07/0.64  fof(f37,plain,(
% 1.07/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f17])).
% 1.07/0.64  fof(f17,plain,(
% 1.07/0.64    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(ennf_transformation,[],[f5])).
% 1.07/0.64  fof(f5,axiom,(
% 1.07/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.07/0.64  fof(f175,plain,(
% 1.07/0.64    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 1.07/0.64    inference(subsumption_resolution,[],[f171,f41])).
% 1.07/0.64  fof(f171,plain,(
% 1.07/0.64    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 1.07/0.64    inference(superposition,[],[f49,f43])).
% 1.07/0.64  fof(f49,plain,(
% 1.07/0.64    ( ! [X4] : (~r1_tarski(k2_relat_1(sK0),k1_relat_1(X4)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X4)) | ~v1_relat_1(X4)) )),
% 1.07/0.64    inference(resolution,[],[f25,f39])).
% 1.07/0.64  fof(f39,plain,(
% 1.07/0.64    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f20])).
% 1.07/0.64  fof(f20,plain,(
% 1.07/0.64    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(flattening,[],[f19])).
% 1.07/0.64  fof(f19,plain,(
% 1.07/0.64    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(ennf_transformation,[],[f6])).
% 1.07/0.64  fof(f6,axiom,(
% 1.07/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.07/0.64  fof(f55,plain,(
% 1.07/0.64    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 1.07/0.64    inference(forward_demodulation,[],[f54,f53])).
% 1.07/0.64  fof(f53,plain,(
% 1.07/0.64    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 1.07/0.64    inference(subsumption_resolution,[],[f52,f26])).
% 1.07/0.64  fof(f26,plain,(
% 1.07/0.64    v1_funct_1(sK0)),
% 1.07/0.64    inference(cnf_transformation,[],[f24])).
% 1.07/0.64  fof(f52,plain,(
% 1.07/0.64    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0)),
% 1.07/0.64    inference(subsumption_resolution,[],[f51,f27])).
% 1.07/0.64  fof(f27,plain,(
% 1.07/0.64    v2_funct_1(sK0)),
% 1.07/0.64    inference(cnf_transformation,[],[f24])).
% 1.07/0.64  fof(f51,plain,(
% 1.07/0.64    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 1.07/0.64    inference(resolution,[],[f25,f40])).
% 1.07/0.64  fof(f40,plain,(
% 1.07/0.64    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.07/0.64    inference(cnf_transformation,[],[f22])).
% 1.07/0.64  fof(f22,plain,(
% 1.07/0.64    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.07/0.64    inference(flattening,[],[f21])).
% 1.07/0.64  fof(f21,plain,(
% 1.07/0.64    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.07/0.64    inference(ennf_transformation,[],[f8])).
% 1.07/0.64  fof(f8,axiom,(
% 1.07/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.07/0.64  fof(f54,plain,(
% 1.07/0.64    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 1.07/0.64    inference(backward_demodulation,[],[f28,f53])).
% 1.07/0.64  fof(f28,plain,(
% 1.07/0.64    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 1.07/0.64    inference(cnf_transformation,[],[f24])).
% 1.07/0.64  % SZS output end Proof for theBenchmark
% 1.07/0.64  % (26845)------------------------------
% 1.07/0.64  % (26845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.07/0.64  % (26845)Termination reason: Refutation
% 1.07/0.64  
% 1.07/0.64  % (26845)Memory used [KB]: 1918
% 1.07/0.64  % (26845)Time elapsed: 0.084 s
% 1.07/0.64  % (26845)------------------------------
% 1.07/0.64  % (26845)------------------------------
% 1.07/0.65  % (26699)Success in time 0.287 s
%------------------------------------------------------------------------------
