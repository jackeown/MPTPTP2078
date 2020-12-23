%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:12 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  105 (1068 expanded)
%              Number of leaves         :   21 ( 320 expanded)
%              Depth                    :   17
%              Number of atoms          :  251 (2997 expanded)
%              Number of equality atoms :  108 ( 769 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1040,f1019])).

fof(f1019,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1018,f261])).

fof(f261,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f256,f255])).

fof(f255,plain,(
    k1_relat_1(sK2) = k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0)) ),
    inference(unit_resulting_resolution,[],[f93,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k6_subset_1(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f126,f168])).

fof(f168,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f113,f106])).

fof(f106,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f93,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f54,f72])).

fof(f72,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f49])).

fof(f49,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f256,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0))) ),
    inference(unit_resulting_resolution,[],[f93,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))) = X0 ) ),
    inference(definition_unfolding,[],[f125,f169])).

fof(f169,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f116,f168])).

fof(f116,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1018,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)),sK1)) ),
    inference(forward_demodulation,[],[f1017,f350])).

fof(f350,plain,(
    k1_relat_1(sK2) = k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK2),sK0)) ),
    inference(backward_demodulation,[],[f255,f347])).

fof(f347,plain,(
    k6_subset_1(k1_relat_1(sK2),sK0) = k5_xboole_0(k1_relat_1(sK2),sK0) ),
    inference(backward_demodulation,[],[f343,f346])).

fof(f346,plain,(
    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f325,f255])).

fof(f325,plain,(
    k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    inference(superposition,[],[f182,f253])).

fof(f253,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f93,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f135,f106])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f182,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k6_subset_1(X1,X0)) = k5_xboole_0(X1,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f107,f168,f168])).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f343,plain,(
    k5_xboole_0(k1_relat_1(sK2),sK0) = k6_subset_1(k5_xboole_0(k1_relat_1(sK2),k1_xboole_0),sK0) ),
    inference(backward_demodulation,[],[f322,f342])).

fof(f342,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f341,f261])).

fof(f341,plain,(
    k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) = k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f323,f255])).

fof(f323,plain,(
    k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0))) = k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(superposition,[],[f181,f253])).

fof(f181,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f105,f169,f169])).

fof(f105,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f322,plain,(
    k5_xboole_0(k1_relat_1(sK2),sK0) = k6_subset_1(k5_xboole_0(k1_relat_1(sK2),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0))) ),
    inference(superposition,[],[f175,f253])).

fof(f175,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k6_subset_1(k5_xboole_0(X0,k6_subset_1(X1,X0)),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0)))) ),
    inference(definition_unfolding,[],[f115,f106,f168,f169])).

fof(f115,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f1017,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK2),sK0))),sK1)) ),
    inference(forward_demodulation,[],[f1016,f347])).

fof(f1016,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0))),sK1)) ),
    inference(forward_demodulation,[],[f1015,f181])).

fof(f1015,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,k1_relat_1(sK2)))),sK1)) ),
    inference(forward_demodulation,[],[f1011,f204])).

fof(f204,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k6_subset_1(X1,X2)),k5_xboole_0(X0,k6_subset_1(k6_subset_1(X1,X2),X0))) = k6_subset_1(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))),X2) ),
    inference(definition_unfolding,[],[f139,f169,f106,f106,f169])).

fof(f139,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1011,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,sK1)),k5_xboole_0(k1_relat_1(sK2),k6_subset_1(k6_subset_1(sK0,sK1),k1_relat_1(sK2))))) ),
    inference(unit_resulting_resolution,[],[f992,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f120,f169])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f992,plain,(
    r1_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f90,f660,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f660,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f250,f271])).

fof(f271,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f92,f200])).

fof(f92,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f73])).

fof(f250,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f90,f91,f94,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f94,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f90,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f1040,plain,(
    ! [X3] : r2_hidden(X3,k6_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f227,f1023])).

fof(f1023,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f252,f1019,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f136,f101])).

fof(f101,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f82])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f252,plain,(
    k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f95,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f134,f106])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f95,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f227,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f226])).

fof(f226,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f198])).

fof(f198,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f131,f101])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f78,f79])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
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
    inference(rectify,[],[f77])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (31119)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (31111)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (31103)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31099)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (31123)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (31104)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (31122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (31106)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (31120)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (31112)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (31107)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (31107)Refutation not found, incomplete strategy% (31107)------------------------------
% 0.21/0.55  % (31107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31107)Memory used [KB]: 10874
% 0.21/0.55  % (31107)Time elapsed: 0.125 s
% 0.21/0.55  % (31107)------------------------------
% 0.21/0.55  % (31107)------------------------------
% 0.21/0.55  % (31124)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.55  % (31108)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.47/0.56  % (31102)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.47/0.56  % (31100)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.47/0.56  % (31114)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.56  % (31101)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.47/0.56  % (31116)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.47/0.56  % (31097)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.58/0.57  % (31098)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.58/0.58  % (31118)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.58/0.58  % (31117)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.58/0.58  % (31105)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.58/0.58  % (31125)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.58/0.58  % (31110)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.58/0.58  % (31121)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.58/0.59  % (31115)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.58/0.59  % (31109)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.58/0.59  % (31126)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.58/0.59  % (31126)Refutation not found, incomplete strategy% (31126)------------------------------
% 1.58/0.59  % (31126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (31126)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (31126)Memory used [KB]: 1663
% 1.58/0.59  % (31126)Time elapsed: 0.177 s
% 1.58/0.59  % (31126)------------------------------
% 1.58/0.59  % (31126)------------------------------
% 1.58/0.60  % (31113)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.58/0.60  % (31113)Refutation not found, incomplete strategy% (31113)------------------------------
% 1.58/0.60  % (31113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (31113)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (31113)Memory used [KB]: 10746
% 1.58/0.60  % (31113)Time elapsed: 0.180 s
% 1.58/0.60  % (31113)------------------------------
% 1.58/0.60  % (31113)------------------------------
% 1.58/0.60  % (31125)Refutation not found, incomplete strategy% (31125)------------------------------
% 1.58/0.60  % (31125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (31125)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (31125)Memory used [KB]: 10874
% 1.58/0.60  % (31125)Time elapsed: 0.187 s
% 1.58/0.60  % (31125)------------------------------
% 1.58/0.60  % (31125)------------------------------
% 2.24/0.66  % (31108)Refutation found. Thanks to Tanya!
% 2.24/0.66  % SZS status Theorem for theBenchmark
% 2.24/0.67  % SZS output start Proof for theBenchmark
% 2.24/0.67  fof(f1096,plain,(
% 2.24/0.67    $false),
% 2.24/0.67    inference(subsumption_resolution,[],[f1040,f1019])).
% 2.24/0.67  fof(f1019,plain,(
% 2.24/0.67    ( ! [X0] : (~r2_hidden(X0,k6_subset_1(sK0,sK1))) )),
% 2.24/0.67    inference(forward_demodulation,[],[f1018,f261])).
% 2.24/0.67  fof(f261,plain,(
% 2.24/0.67    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))),
% 2.24/0.67    inference(backward_demodulation,[],[f256,f255])).
% 2.24/0.67  fof(f255,plain,(
% 2.24/0.67    k1_relat_1(sK2) = k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0))),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f93,f194])).
% 2.24/0.67  fof(f194,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k6_subset_1(X1,X0)) = X1) )),
% 2.24/0.67    inference(definition_unfolding,[],[f126,f168])).
% 2.24/0.67  fof(f168,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 2.24/0.67    inference(definition_unfolding,[],[f113,f106])).
% 2.24/0.67  fof(f106,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f40])).
% 2.24/0.67  fof(f40,axiom,(
% 2.24/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.24/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.24/0.67  fof(f113,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.24/0.67    inference(cnf_transformation,[],[f22])).
% 2.24/0.67  fof(f22,axiom,(
% 2.24/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.24/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.24/0.67  fof(f126,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f61])).
% 2.24/0.67  fof(f61,plain,(
% 2.24/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f9])).
% 2.24/0.67  fof(f9,axiom,(
% 2.24/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.24/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.24/0.67  fof(f93,plain,(
% 2.24/0.67    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.24/0.67    inference(cnf_transformation,[],[f73])).
% 2.24/0.67  fof(f73,plain,(
% 2.24/0.67    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.24/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f54,f72])).
% 2.24/0.67  fof(f72,plain,(
% 2.24/0.67    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.24/0.67    introduced(choice_axiom,[])).
% 2.24/0.67  fof(f54,plain,(
% 2.24/0.67    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.24/0.67    inference(flattening,[],[f53])).
% 2.24/0.67  fof(f53,plain,(
% 2.24/0.67    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.24/0.67    inference(ennf_transformation,[],[f50])).
% 2.24/0.67  fof(f50,negated_conjecture,(
% 2.24/0.67    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.24/0.67    inference(negated_conjecture,[],[f49])).
% 2.24/0.67  fof(f49,conjecture,(
% 2.24/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.24/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 2.24/0.67  fof(f256,plain,(
% 2.24/0.67    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0)))),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f93,f193])).
% 2.24/0.67  fof(f193,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))) = X0) )),
% 2.24/0.67    inference(definition_unfolding,[],[f125,f169])).
% 2.24/0.67  fof(f169,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0)))) )),
% 2.24/0.67    inference(definition_unfolding,[],[f116,f168])).
% 2.24/0.67  fof(f116,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.24/0.67    inference(cnf_transformation,[],[f21])).
% 2.24/0.67  fof(f21,axiom,(
% 2.24/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.24/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.24/0.67  fof(f125,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f60])).
% 2.24/0.67  fof(f60,plain,(
% 2.24/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f12])).
% 2.24/0.67  fof(f12,axiom,(
% 2.24/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.24/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.24/0.67  fof(f1018,plain,(
% 2.24/0.67    ( ! [X0] : (~r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)),sK1))) )),
% 2.24/0.67    inference(forward_demodulation,[],[f1017,f350])).
% 2.24/0.67  fof(f350,plain,(
% 2.24/0.67    k1_relat_1(sK2) = k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK2),sK0))),
% 2.24/0.67    inference(backward_demodulation,[],[f255,f347])).
% 2.24/0.67  fof(f347,plain,(
% 2.24/0.67    k6_subset_1(k1_relat_1(sK2),sK0) = k5_xboole_0(k1_relat_1(sK2),sK0)),
% 2.24/0.67    inference(backward_demodulation,[],[f343,f346])).
% 2.24/0.67  fof(f346,plain,(
% 2.24/0.67    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)),
% 2.24/0.67    inference(forward_demodulation,[],[f325,f255])).
% 2.24/0.67  fof(f325,plain,(
% 2.24/0.67    k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)),
% 2.24/0.67    inference(superposition,[],[f182,f253])).
% 2.24/0.67  fof(f253,plain,(
% 2.24/0.67    k1_xboole_0 = k6_subset_1(sK0,k1_relat_1(sK2))),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f93,f200])).
% 2.24/0.67  fof(f200,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.24/0.67    inference(definition_unfolding,[],[f135,f106])).
% 2.24/0.68  fof(f135,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f81])).
% 2.24/0.68  fof(f81,plain,(
% 2.24/0.68    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.24/0.68    inference(nnf_transformation,[],[f5])).
% 2.24/0.68  fof(f5,axiom,(
% 2.24/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.24/0.68  fof(f182,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k6_subset_1(X1,X0)) = k5_xboole_0(X1,k6_subset_1(X0,X1))) )),
% 2.24/0.68    inference(definition_unfolding,[],[f107,f168,f168])).
% 2.24/0.68  fof(f107,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f1])).
% 2.24/0.68  fof(f1,axiom,(
% 2.24/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.24/0.68  fof(f343,plain,(
% 2.24/0.68    k5_xboole_0(k1_relat_1(sK2),sK0) = k6_subset_1(k5_xboole_0(k1_relat_1(sK2),k1_xboole_0),sK0)),
% 2.24/0.68    inference(backward_demodulation,[],[f322,f342])).
% 2.24/0.68  fof(f342,plain,(
% 2.24/0.68    sK0 = k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0))),
% 2.24/0.68    inference(forward_demodulation,[],[f341,f261])).
% 2.24/0.68  fof(f341,plain,(
% 2.24/0.68    k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) = k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0))),
% 2.24/0.68    inference(forward_demodulation,[],[f323,f255])).
% 2.24/0.68  fof(f323,plain,(
% 2.24/0.68    k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0))) = k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0))),
% 2.24/0.68    inference(superposition,[],[f181,f253])).
% 2.24/0.68  fof(f181,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k6_subset_1(X0,X1)))) )),
% 2.24/0.68    inference(definition_unfolding,[],[f105,f169,f169])).
% 2.24/0.68  fof(f105,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f2])).
% 2.24/0.68  fof(f2,axiom,(
% 2.24/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.24/0.68  fof(f322,plain,(
% 2.24/0.68    k5_xboole_0(k1_relat_1(sK2),sK0) = k6_subset_1(k5_xboole_0(k1_relat_1(sK2),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)))),
% 2.24/0.68    inference(superposition,[],[f175,f253])).
% 2.24/0.68  fof(f175,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k6_subset_1(k5_xboole_0(X0,k6_subset_1(X1,X0)),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))))) )),
% 2.24/0.68    inference(definition_unfolding,[],[f115,f106,f168,f169])).
% 2.24/0.68  fof(f115,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.24/0.68    inference(cnf_transformation,[],[f6])).
% 2.24/0.68  fof(f6,axiom,(
% 2.24/0.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.24/0.68  fof(f1017,plain,(
% 2.24/0.68    ( ! [X0] : (~r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK2),sK0))),sK1))) )),
% 2.24/0.68    inference(forward_demodulation,[],[f1016,f347])).
% 2.24/0.68  fof(f1016,plain,(
% 2.24/0.68    ( ! [X0] : (~r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK2)),k5_xboole_0(sK0,k6_subset_1(k1_relat_1(sK2),sK0))),sK1))) )),
% 2.24/0.68    inference(forward_demodulation,[],[f1015,f181])).
% 2.24/0.68  fof(f1015,plain,(
% 2.24/0.68    ( ! [X0] : (~r2_hidden(X0,k6_subset_1(k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),sK0),k5_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,k1_relat_1(sK2)))),sK1))) )),
% 2.24/0.68    inference(forward_demodulation,[],[f1011,f204])).
% 2.24/0.68  fof(f204,plain,(
% 2.24/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k6_subset_1(X1,X2)),k5_xboole_0(X0,k6_subset_1(k6_subset_1(X1,X2),X0))) = k6_subset_1(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0))),X2)) )),
% 2.24/0.68    inference(definition_unfolding,[],[f139,f169,f106,f106,f169])).
% 2.24/0.68  fof(f139,plain,(
% 2.24/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f16])).
% 2.24/0.68  fof(f16,axiom,(
% 2.24/0.68    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.24/0.68  fof(f1011,plain,(
% 2.24/0.68    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k5_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,sK1)),k5_xboole_0(k1_relat_1(sK2),k6_subset_1(k6_subset_1(sK0,sK1),k1_relat_1(sK2)))))) )),
% 2.24/0.68    inference(unit_resulting_resolution,[],[f992,f190])).
% 2.24/0.68  fof(f190,plain,(
% 2.24/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k6_subset_1(X1,X0)))) | ~r1_xboole_0(X0,X1)) )),
% 2.24/0.68    inference(definition_unfolding,[],[f120,f169])).
% 2.24/0.68  fof(f120,plain,(
% 2.24/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.24/0.68    inference(cnf_transformation,[],[f75])).
% 2.24/0.68  fof(f75,plain,(
% 2.24/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.24/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f74])).
% 2.24/0.68  fof(f74,plain,(
% 2.24/0.68    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.24/0.68    introduced(choice_axiom,[])).
% 2.24/0.68  fof(f56,plain,(
% 2.24/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.24/0.68    inference(ennf_transformation,[],[f52])).
% 2.24/0.68  fof(f52,plain,(
% 2.24/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.24/0.68    inference(rectify,[],[f4])).
% 2.24/0.68  fof(f4,axiom,(
% 2.24/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.24/0.68  fof(f992,plain,(
% 2.24/0.68    r1_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,sK1))),
% 2.24/0.68    inference(unit_resulting_resolution,[],[f90,f660,f122])).
% 2.24/0.68  fof(f122,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f76])).
% 2.24/0.68  fof(f76,plain,(
% 2.24/0.68    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.24/0.68    inference(nnf_transformation,[],[f58])).
% 2.24/0.68  fof(f58,plain,(
% 2.24/0.68    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.24/0.68    inference(ennf_transformation,[],[f44])).
% 2.24/0.68  fof(f44,axiom,(
% 2.24/0.68    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 2.24/0.68  fof(f660,plain,(
% 2.24/0.68    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 2.24/0.68    inference(superposition,[],[f250,f271])).
% 2.24/0.68  fof(f271,plain,(
% 2.24/0.68    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.24/0.68    inference(unit_resulting_resolution,[],[f92,f200])).
% 2.24/0.68  fof(f92,plain,(
% 2.24/0.68    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.24/0.68    inference(cnf_transformation,[],[f73])).
% 2.24/0.68  fof(f250,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 2.24/0.68    inference(unit_resulting_resolution,[],[f90,f91,f94,f144])).
% 2.24/0.68  fof(f144,plain,(
% 2.24/0.68    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f69])).
% 2.24/0.68  fof(f69,plain,(
% 2.24/0.68    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.24/0.68    inference(flattening,[],[f68])).
% 2.24/0.68  fof(f68,plain,(
% 2.24/0.68    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.24/0.68    inference(ennf_transformation,[],[f47])).
% 2.24/0.68  fof(f47,axiom,(
% 2.24/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 2.24/0.68  fof(f94,plain,(
% 2.24/0.68    v2_funct_1(sK2)),
% 2.24/0.68    inference(cnf_transformation,[],[f73])).
% 2.24/0.68  fof(f91,plain,(
% 2.24/0.68    v1_funct_1(sK2)),
% 2.24/0.68    inference(cnf_transformation,[],[f73])).
% 2.24/0.68  fof(f90,plain,(
% 2.24/0.68    v1_relat_1(sK2)),
% 2.24/0.68    inference(cnf_transformation,[],[f73])).
% 2.24/0.68  fof(f1040,plain,(
% 2.24/0.68    ( ! [X3] : (r2_hidden(X3,k6_subset_1(sK0,sK1))) )),
% 2.24/0.68    inference(backward_demodulation,[],[f227,f1023])).
% 2.24/0.68  fof(f1023,plain,(
% 2.24/0.68    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k6_subset_1(sK0,sK1)) )),
% 2.24/0.68    inference(unit_resulting_resolution,[],[f252,f1019,f203])).
% 2.24/0.68  fof(f203,plain,(
% 2.24/0.68    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 2.24/0.68    inference(definition_unfolding,[],[f136,f101])).
% 2.24/0.68  fof(f101,plain,(
% 2.24/0.68    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.24/0.68    inference(cnf_transformation,[],[f31])).
% 2.24/0.68  fof(f31,axiom,(
% 2.24/0.68    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 2.24/0.68  fof(f136,plain,(
% 2.24/0.68    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.24/0.68    inference(cnf_transformation,[],[f83])).
% 2.24/0.68  fof(f83,plain,(
% 2.24/0.68    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.24/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f82])).
% 2.24/0.68  fof(f82,plain,(
% 2.24/0.68    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 2.24/0.68    introduced(choice_axiom,[])).
% 2.24/0.68  fof(f65,plain,(
% 2.24/0.68    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.24/0.68    inference(ennf_transformation,[],[f37])).
% 2.24/0.68  fof(f37,axiom,(
% 2.24/0.68    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 2.24/0.68  fof(f252,plain,(
% 2.24/0.68    k1_xboole_0 != k6_subset_1(sK0,sK1)),
% 2.24/0.68    inference(unit_resulting_resolution,[],[f95,f201])).
% 2.24/0.68  fof(f201,plain,(
% 2.24/0.68    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.24/0.68    inference(definition_unfolding,[],[f134,f106])).
% 2.24/0.68  fof(f134,plain,(
% 2.24/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.24/0.68    inference(cnf_transformation,[],[f81])).
% 2.24/0.68  fof(f95,plain,(
% 2.24/0.68    ~r1_tarski(sK0,sK1)),
% 2.24/0.68    inference(cnf_transformation,[],[f73])).
% 2.24/0.68  fof(f227,plain,(
% 2.24/0.68    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 2.24/0.68    inference(equality_resolution,[],[f226])).
% 2.24/0.68  fof(f226,plain,(
% 2.24/0.68    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 2.24/0.68    inference(equality_resolution,[],[f198])).
% 2.24/0.68  fof(f198,plain,(
% 2.24/0.68    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 2.24/0.68    inference(definition_unfolding,[],[f131,f101])).
% 2.24/0.68  fof(f131,plain,(
% 2.24/0.68    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.24/0.68    inference(cnf_transformation,[],[f80])).
% 2.24/0.68  fof(f80,plain,(
% 2.24/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.24/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f78,f79])).
% 2.24/0.68  fof(f79,plain,(
% 2.24/0.68    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 2.24/0.68    introduced(choice_axiom,[])).
% 2.24/0.68  fof(f78,plain,(
% 2.24/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.24/0.68    inference(rectify,[],[f77])).
% 2.24/0.68  fof(f77,plain,(
% 2.24/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.24/0.68    inference(nnf_transformation,[],[f23])).
% 2.24/0.68  fof(f23,axiom,(
% 2.24/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.24/0.68  % SZS output end Proof for theBenchmark
% 2.24/0.68  % (31108)------------------------------
% 2.24/0.68  % (31108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.68  % (31108)Termination reason: Refutation
% 2.24/0.68  
% 2.24/0.68  % (31108)Memory used [KB]: 7291
% 2.24/0.68  % (31108)Time elapsed: 0.230 s
% 2.24/0.68  % (31108)------------------------------
% 2.24/0.68  % (31108)------------------------------
% 2.24/0.68  % (31096)Success in time 0.316 s
%------------------------------------------------------------------------------
