%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0699+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 28.84s
% Output     : Refutation 28.84s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 161 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 537 expanded)
%              Number of equality atoms :   82 ( 180 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41843,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41793,f2862])).

fof(f2862,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f2861])).

fof(f2861,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f2518])).

fof(f2518,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1845])).

fof(f1845,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK109(X0,X1) != X0
            | ~ r2_hidden(sK109(X0,X1),X1) )
          & ( sK109(X0,X1) = X0
            | r2_hidden(sK109(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK109])],[f1843,f1844])).

fof(f1844,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK109(X0,X1) != X0
          | ~ r2_hidden(sK109(X0,X1),X1) )
        & ( sK109(X0,X1) = X0
          | r2_hidden(sK109(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1843,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f1842])).

fof(f1842,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f41793,plain,(
    ~ r2_hidden(k9_relat_1(sK16,sK15),k1_tarski(k9_relat_1(sK16,sK15))) ),
    inference(backward_demodulation,[],[f8790,f41751])).

fof(f41751,plain,(
    ! [X0] : k9_relat_1(sK16,X0) = k10_relat_1(k4_relat_1(sK16),X0) ),
    inference(forward_demodulation,[],[f41684,f7239])).

fof(f7239,plain,(
    ! [X0] : k9_relat_1(sK16,X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK16,X0))) ),
    inference(backward_demodulation,[],[f5757,f7192])).

fof(f7192,plain,(
    ! [X0] : k9_relat_1(sK16,X0) = k2_relat_1(k7_relat_1(sK16,X0)) ),
    inference(unit_resulting_resolution,[],[f1953,f2071])).

fof(f2071,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1127,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1953,plain,(
    v1_relat_1(sK16) ),
    inference(cnf_transformation,[],[f1615])).

fof(f1615,plain,
    ( k9_relat_1(sK16,sK15) != k10_relat_1(k2_funct_1(sK16),sK15)
    & v2_funct_1(sK16)
    & v1_funct_1(sK16)
    & v1_relat_1(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f1021,f1614])).

fof(f1614,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK16,sK15) != k10_relat_1(k2_funct_1(sK16),sK15)
      & v2_funct_1(sK16)
      & v1_funct_1(sK16)
      & v1_relat_1(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f1021,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1020])).

fof(f1020,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f956])).

fof(f956,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f955])).

fof(f955,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f5757,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK16,X0)) = k1_relat_1(k4_relat_1(k7_relat_1(sK16,X0))) ),
    inference(unit_resulting_resolution,[],[f3145,f2652])).

fof(f2652,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f1491])).

fof(f1491,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f838])).

fof(f838,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f3145,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK16,X0)) ),
    inference(unit_resulting_resolution,[],[f1953,f2389])).

fof(f2389,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1297])).

fof(f1297,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f669])).

fof(f669,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f41684,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK16),X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK16,X0))) ),
    inference(backward_demodulation,[],[f19655,f41675])).

fof(f41675,plain,(
    ! [X0] : k8_relat_1(X0,k4_relat_1(sK16)) = k4_relat_1(k7_relat_1(sK16,X0)) ),
    inference(backward_demodulation,[],[f8049,f41674])).

fof(f41674,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK16),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(sK16,X0)) ),
    inference(forward_demodulation,[],[f41673,f7946])).

fof(f7946,plain,(
    ! [X0] : k7_relat_1(sK16,X0) = k5_relat_1(k6_relat_1(X0),sK16) ),
    inference(unit_resulting_resolution,[],[f1953,f2628])).

fof(f2628,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f1476])).

fof(f1476,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f41673,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK16),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),sK16)) ),
    inference(forward_demodulation,[],[f41340,f2658])).

fof(f2658,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f864])).

fof(f864,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f41340,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(k6_relat_1(X0),sK16)) = k5_relat_1(k4_relat_1(sK16),k4_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f2131,f1953,f2650])).

fof(f2650,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f1489,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f853])).

fof(f853,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f2131,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f907])).

fof(f907,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f8049,plain,(
    ! [X0] : k8_relat_1(X0,k4_relat_1(sK16)) = k5_relat_1(k4_relat_1(sK16),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f2980,f2629])).

fof(f2629,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f1477])).

fof(f1477,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f726])).

fof(f726,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f2980,plain,(
    v1_relat_1(k4_relat_1(sK16)) ),
    inference(unit_resulting_resolution,[],[f1953,f2655])).

fof(f2655,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1493])).

fof(f1493,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f666])).

fof(f666,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f19655,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK16),X0) = k1_relat_1(k8_relat_1(X0,k4_relat_1(sK16))) ),
    inference(forward_demodulation,[],[f19654,f8049])).

fof(f19654,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK16),X0) = k1_relat_1(k5_relat_1(k4_relat_1(sK16),k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f18534,f2634])).

fof(f2634,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f18534,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK16),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK16),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f2980,f2131,f2004])).

fof(f2004,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f1068])).

fof(f1068,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f784])).

fof(f784,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f8790,plain,(
    ~ r2_hidden(k10_relat_1(k4_relat_1(sK16),sK15),k1_tarski(k9_relat_1(sK16,sK15))) ),
    inference(backward_demodulation,[],[f3812,f8756])).

fof(f8756,plain,(
    k2_funct_1(sK16) = k4_relat_1(sK16) ),
    inference(unit_resulting_resolution,[],[f1953,f1954,f1955,f2043])).

fof(f2043,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1096])).

fof(f1096,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1095])).

fof(f1095,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1955,plain,(
    v2_funct_1(sK16) ),
    inference(cnf_transformation,[],[f1615])).

fof(f1954,plain,(
    v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f1615])).

fof(f3812,plain,(
    ~ r2_hidden(k10_relat_1(k2_funct_1(sK16),sK15),k1_tarski(k9_relat_1(sK16,sK15))) ),
    inference(unit_resulting_resolution,[],[f1956,f2863])).

fof(f2863,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f2517])).

fof(f2517,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1845])).

fof(f1956,plain,(
    k9_relat_1(sK16,sK15) != k10_relat_1(k2_funct_1(sK16),sK15) ),
    inference(cnf_transformation,[],[f1615])).
%------------------------------------------------------------------------------
