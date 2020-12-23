%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:09 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 410 expanded)
%              Number of leaves         :   32 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          :  367 (1148 expanded)
%              Number of equality atoms :   59 ( 217 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f887,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f208,f882,f761])).

fof(f761,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(sK0),X7)
      | ~ r1_tarski(k1_relat_1(sK1),X7) ) ),
    inference(subsumption_resolution,[],[f756,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f756,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_xboole_0,X7)
      | r1_tarski(k1_relat_1(sK0),X7)
      | ~ r1_tarski(k1_relat_1(sK1),X7) ) ),
    inference(superposition,[],[f271,f385])).

fof(f385,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f368,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f92,f74])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f368,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f367,f170])).

fof(f170,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f163,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f163,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f159,f125])).

fof(f125,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f159,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f158,f73])).

fof(f73,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f158,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f110,f154])).

fof(f154,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(resolution,[],[f135,f73])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1)) ) ),
    inference(resolution,[],[f110,f79])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f106])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f82,f84])).

fof(f84,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f367,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f366,f70])).

fof(f70,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f366,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f257,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f98,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f257,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f201,f68])).

fof(f68,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f201,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1))) ) ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f271,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k6_subset_1(X5,X3),X4)
      | r1_tarski(X5,X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f117,f226])).

fof(f226,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f225,f122])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f225,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f120,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK8(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f105,f107])).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK8(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK8(X0,X1,X2))
        & r1_tarski(X2,sK8(X0,X1,X2))
        & r1_tarski(X0,sK8(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK8(X0,X1,X2))
        & r1_tarski(X2,sK8(X0,X1,X2))
        & r1_tarski(X0,sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK8(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f104,f107])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X2,sK8(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f101,f107,f81])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f882,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f833,f507])).

fof(f507,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f191,f71])).

fof(f71,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f191,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f118,f180])).

fof(f180,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f108,f68])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f76,f107])).

fof(f76,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f102,f107])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f833,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f830,f122])).

fof(f830,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f762,f207])).

fof(f207,plain,(
    ! [X2] :
      ( r1_tarski(X2,k3_relat_1(sK1))
      | ~ r1_tarski(X2,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f115,f181])).

fof(f181,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f108,f69])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f99,f107])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f762,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_relat_1(sK1),X10)
      | r1_tarski(k2_relat_1(sK0),X10) ) ),
    inference(subsumption_resolution,[],[f759,f74])).

fof(f759,plain,(
    ! [X10] :
      ( ~ r1_tarski(k1_xboole_0,X10)
      | r1_tarski(k2_relat_1(sK0),X10)
      | ~ r1_tarski(k2_relat_1(sK1),X10) ) ),
    inference(superposition,[],[f271,f295])).

fof(f295,plain,(
    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f294,f130])).

fof(f294,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f293,f184])).

fof(f184,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f179,f79])).

fof(f179,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f178,f72])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f178,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f171,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f171,plain,(
    ! [X3] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X3,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f163,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK4(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f293,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f292,f70])).

fof(f292,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f243,f113])).

fof(f243,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f196,f68])).

fof(f196,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X1,sK1))) ) ),
    inference(resolution,[],[f77,f69])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f208,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f109,f181])).

fof(f109,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f80,f107])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (8636)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (8643)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (8634)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (8645)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (8631)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (8654)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (8659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (8651)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (8646)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (8653)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (8637)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8659)Refutation not found, incomplete strategy% (8659)------------------------------
% 0.21/0.53  % (8659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8635)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (8659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8659)Memory used [KB]: 10746
% 0.21/0.53  % (8659)Time elapsed: 0.121 s
% 0.21/0.53  % (8659)------------------------------
% 0.21/0.53  % (8659)------------------------------
% 0.21/0.53  % (8641)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (8638)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (8633)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (8632)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8657)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (8639)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (8656)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (8658)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (8647)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (8650)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (8648)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (8647)Refutation not found, incomplete strategy% (8647)------------------------------
% 0.21/0.55  % (8647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8655)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8640)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (8660)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (8642)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (8649)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (8644)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (8652)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (8647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8647)Memory used [KB]: 10618
% 0.21/0.56  % (8647)Time elapsed: 0.140 s
% 0.21/0.56  % (8647)------------------------------
% 0.21/0.56  % (8647)------------------------------
% 0.21/0.56  % (8641)Refutation not found, incomplete strategy% (8641)------------------------------
% 0.21/0.56  % (8641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8641)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8641)Memory used [KB]: 10746
% 0.21/0.56  % (8641)Time elapsed: 0.149 s
% 0.21/0.56  % (8641)------------------------------
% 0.21/0.56  % (8641)------------------------------
% 1.54/0.57  % (8660)Refutation not found, incomplete strategy% (8660)------------------------------
% 1.54/0.57  % (8660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (8660)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (8660)Memory used [KB]: 1663
% 1.54/0.57  % (8660)Time elapsed: 0.147 s
% 1.54/0.57  % (8660)------------------------------
% 1.54/0.57  % (8660)------------------------------
% 2.11/0.66  % (8653)Refutation found. Thanks to Tanya!
% 2.11/0.66  % SZS status Theorem for theBenchmark
% 2.11/0.66  % SZS output start Proof for theBenchmark
% 2.11/0.66  fof(f887,plain,(
% 2.11/0.66    $false),
% 2.11/0.66    inference(unit_resulting_resolution,[],[f208,f882,f761])).
% 2.11/0.66  fof(f761,plain,(
% 2.11/0.66    ( ! [X7] : (r1_tarski(k1_relat_1(sK0),X7) | ~r1_tarski(k1_relat_1(sK1),X7)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f756,f74])).
% 2.11/0.66  fof(f74,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f10])).
% 2.11/0.66  fof(f10,axiom,(
% 2.11/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.11/0.66  fof(f756,plain,(
% 2.11/0.66    ( ! [X7] : (~r1_tarski(k1_xboole_0,X7) | r1_tarski(k1_relat_1(sK0),X7) | ~r1_tarski(k1_relat_1(sK1),X7)) )),
% 2.11/0.66    inference(superposition,[],[f271,f385])).
% 2.11/0.66  fof(f385,plain,(
% 2.11/0.66    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.11/0.66    inference(resolution,[],[f368,f130])).
% 2.11/0.66  fof(f130,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.11/0.66    inference(resolution,[],[f92,f74])).
% 2.11/0.66  fof(f92,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f58])).
% 2.11/0.66  fof(f58,plain,(
% 2.11/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.66    inference(flattening,[],[f57])).
% 2.11/0.66  fof(f57,plain,(
% 2.11/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.66    inference(nnf_transformation,[],[f5])).
% 2.11/0.66  fof(f5,axiom,(
% 2.11/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.66  fof(f368,plain,(
% 2.11/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.11/0.66    inference(forward_demodulation,[],[f367,f170])).
% 2.11/0.66  fof(f170,plain,(
% 2.11/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.11/0.66    inference(resolution,[],[f163,f79])).
% 2.11/0.66  fof(f79,plain,(
% 2.11/0.66    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.11/0.66    inference(cnf_transformation,[],[f52])).
% 2.11/0.66  fof(f52,plain,(
% 2.11/0.66    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f51])).
% 2.11/0.66  fof(f51,plain,(
% 2.11/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f35,plain,(
% 2.11/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.11/0.66    inference(ennf_transformation,[],[f4])).
% 2.11/0.66  fof(f4,axiom,(
% 2.11/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.11/0.66  fof(f163,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.11/0.66    inference(resolution,[],[f159,f125])).
% 2.11/0.66  fof(f125,plain,(
% 2.11/0.66    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.11/0.66    inference(equality_resolution,[],[f93])).
% 2.11/0.66  fof(f93,plain,(
% 2.11/0.66    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.11/0.66    inference(cnf_transformation,[],[f64])).
% 2.11/0.66  fof(f64,plain,(
% 2.11/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).
% 2.11/0.66  fof(f61,plain,(
% 2.11/0.66    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f62,plain,(
% 2.11/0.66    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f63,plain,(
% 2.11/0.66    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f60,plain,(
% 2.11/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.11/0.66    inference(rectify,[],[f59])).
% 2.11/0.66  fof(f59,plain,(
% 2.11/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.11/0.66    inference(nnf_transformation,[],[f21])).
% 2.11/0.66  fof(f21,axiom,(
% 2.11/0.66    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.11/0.66  fof(f159,plain,(
% 2.11/0.66    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f158,f73])).
% 2.11/0.66  fof(f73,plain,(
% 2.11/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f13])).
% 2.11/0.66  fof(f13,axiom,(
% 2.11/0.66    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.11/0.66  fof(f158,plain,(
% 2.11/0.66    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 2.11/0.66    inference(superposition,[],[f110,f154])).
% 2.11/0.66  fof(f154,plain,(
% 2.11/0.66    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 2.11/0.66    inference(resolution,[],[f135,f73])).
% 2.11/0.66  fof(f135,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.11/0.66    inference(resolution,[],[f110,f79])).
% 2.11/0.66  fof(f110,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.11/0.66    inference(definition_unfolding,[],[f86,f106])).
% 2.11/0.66  fof(f106,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.11/0.66    inference(definition_unfolding,[],[f82,f84])).
% 2.11/0.66  fof(f84,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f16])).
% 2.11/0.66  fof(f16,axiom,(
% 2.11/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.11/0.66  fof(f82,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f19])).
% 2.11/0.66  fof(f19,axiom,(
% 2.11/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.11/0.66  fof(f86,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f54])).
% 2.11/0.66  fof(f54,plain,(
% 2.11/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f53])).
% 2.11/0.66  fof(f53,plain,(
% 2.11/0.66    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f36,plain,(
% 2.11/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/0.66    inference(ennf_transformation,[],[f28])).
% 2.11/0.66  fof(f28,plain,(
% 2.11/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/0.66    inference(rectify,[],[f3])).
% 2.11/0.66  fof(f3,axiom,(
% 2.11/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.11/0.66  fof(f367,plain,(
% 2.11/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.11/0.66    inference(subsumption_resolution,[],[f366,f70])).
% 2.11/0.66  fof(f70,plain,(
% 2.11/0.66    r1_tarski(sK0,sK1)),
% 2.11/0.66    inference(cnf_transformation,[],[f50])).
% 2.11/0.66  fof(f50,plain,(
% 2.11/0.66    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f49,f48])).
% 2.11/0.66  fof(f48,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f49,plain,(
% 2.11/0.66    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f30,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/0.66    inference(flattening,[],[f29])).
% 2.11/0.66  fof(f29,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/0.66    inference(ennf_transformation,[],[f27])).
% 2.11/0.66  fof(f27,negated_conjecture,(
% 2.11/0.66    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.11/0.66    inference(negated_conjecture,[],[f26])).
% 2.11/0.66  fof(f26,conjecture,(
% 2.11/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.11/0.66  fof(f366,plain,(
% 2.11/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~r1_tarski(sK0,sK1)),
% 2.11/0.66    inference(superposition,[],[f257,f113])).
% 2.11/0.66  fof(f113,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(definition_unfolding,[],[f98,f81])).
% 2.11/0.66  fof(f81,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f18])).
% 2.11/0.66  fof(f18,axiom,(
% 2.11/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.11/0.66  fof(f98,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f65])).
% 2.11/0.66  fof(f65,plain,(
% 2.11/0.66    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.11/0.66    inference(nnf_transformation,[],[f6])).
% 2.11/0.66  fof(f6,axiom,(
% 2.11/0.66    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.11/0.66  fof(f257,plain,(
% 2.11/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 2.11/0.66    inference(resolution,[],[f201,f68])).
% 2.11/0.66  fof(f68,plain,(
% 2.11/0.66    v1_relat_1(sK0)),
% 2.11/0.66    inference(cnf_transformation,[],[f50])).
% 2.11/0.66  fof(f201,plain,(
% 2.11/0.66    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1)))) )),
% 2.11/0.66    inference(resolution,[],[f78,f69])).
% 2.11/0.66  fof(f69,plain,(
% 2.11/0.66    v1_relat_1(sK1)),
% 2.11/0.66    inference(cnf_transformation,[],[f50])).
% 2.11/0.66  fof(f78,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f34])).
% 2.11/0.66  fof(f34,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/0.66    inference(ennf_transformation,[],[f23])).
% 2.11/0.66  fof(f23,axiom,(
% 2.11/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 2.11/0.66  fof(f271,plain,(
% 2.11/0.66    ( ! [X4,X5,X3] : (~r1_tarski(k6_subset_1(X5,X3),X4) | r1_tarski(X5,X4) | ~r1_tarski(X3,X4)) )),
% 2.11/0.66    inference(superposition,[],[f117,f226])).
% 2.11/0.66  fof(f226,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f225,f122])).
% 2.11/0.66  fof(f122,plain,(
% 2.11/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.11/0.66    inference(equality_resolution,[],[f91])).
% 2.11/0.66  fof(f91,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.11/0.66    inference(cnf_transformation,[],[f58])).
% 2.11/0.66  fof(f225,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f223])).
% 2.11/0.66  fof(f223,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(resolution,[],[f120,f119])).
% 2.11/0.67  fof(f119,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK8(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f105,f107])).
% 2.11/0.67  fof(f107,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f83,f84])).
% 2.11/0.67  fof(f83,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f17])).
% 2.11/0.67  fof(f17,axiom,(
% 2.11/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.11/0.67  fof(f105,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK8(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f67])).
% 2.11/0.67  fof(f67,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK8(X0,X1,X2)) & r1_tarski(X2,sK8(X0,X1,X2)) & r1_tarski(X0,sK8(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f66])).
% 2.11/0.67  fof(f66,plain,(
% 2.11/0.67    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK8(X0,X1,X2)) & r1_tarski(X2,sK8(X0,X1,X2)) & r1_tarski(X0,sK8(X0,X1,X2))))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f47,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(flattening,[],[f46])).
% 2.11/0.67  fof(f46,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(ennf_transformation,[],[f8])).
% 2.11/0.67  fof(f8,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 2.11/0.67  fof(f120,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X2,sK8(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f104,f107])).
% 2.11/0.67  fof(f104,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X2,sK8(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f67])).
% 2.11/0.67  fof(f117,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f101,f107,f81])).
% 2.11/0.67  fof(f101,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f43])).
% 2.11/0.67  fof(f43,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.11/0.67    inference(ennf_transformation,[],[f12])).
% 2.11/0.67  fof(f12,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.11/0.67  fof(f882,plain,(
% 2.11/0.67    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f833,f507])).
% 2.11/0.67  fof(f507,plain,(
% 2.11/0.67    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f191,f71])).
% 2.11/0.67  fof(f71,plain,(
% 2.11/0.67    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(cnf_transformation,[],[f50])).
% 2.11/0.67  fof(f191,plain,(
% 2.11/0.67    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f118,f180])).
% 2.11/0.67  fof(f180,plain,(
% 2.11/0.67    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.11/0.67    inference(resolution,[],[f108,f68])).
% 2.11/0.67  fof(f108,plain,(
% 2.11/0.67    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f76,f107])).
% 2.11/0.67  fof(f76,plain,(
% 2.11/0.67    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f32])).
% 2.11/0.67  fof(f32,plain,(
% 2.11/0.67    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f22])).
% 2.11/0.67  fof(f22,axiom,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.11/0.67  fof(f118,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f102,f107])).
% 2.11/0.67  fof(f102,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f45])).
% 2.11/0.67  fof(f45,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(flattening,[],[f44])).
% 2.11/0.67  fof(f44,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(ennf_transformation,[],[f15])).
% 2.11/0.67  fof(f15,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.11/0.67  fof(f833,plain,(
% 2.11/0.67    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(subsumption_resolution,[],[f830,f122])).
% 2.11/0.67  fof(f830,plain,(
% 2.11/0.67    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f762,f207])).
% 2.11/0.67  fof(f207,plain,(
% 2.11/0.67    ( ! [X2] : (r1_tarski(X2,k3_relat_1(sK1)) | ~r1_tarski(X2,k2_relat_1(sK1))) )),
% 2.11/0.67    inference(superposition,[],[f115,f181])).
% 2.11/0.67  fof(f181,plain,(
% 2.11/0.67    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.11/0.67    inference(resolution,[],[f108,f69])).
% 2.11/0.67  fof(f115,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f99,f107])).
% 2.11/0.67  fof(f99,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f41])).
% 2.11/0.67  fof(f41,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(ennf_transformation,[],[f7])).
% 2.11/0.67  fof(f7,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.11/0.67  fof(f762,plain,(
% 2.11/0.67    ( ! [X10] : (~r1_tarski(k2_relat_1(sK1),X10) | r1_tarski(k2_relat_1(sK0),X10)) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f759,f74])).
% 2.11/0.67  fof(f759,plain,(
% 2.11/0.67    ( ! [X10] : (~r1_tarski(k1_xboole_0,X10) | r1_tarski(k2_relat_1(sK0),X10) | ~r1_tarski(k2_relat_1(sK1),X10)) )),
% 2.11/0.67    inference(superposition,[],[f271,f295])).
% 2.11/0.67  fof(f295,plain,(
% 2.11/0.67    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f294,f130])).
% 2.11/0.67  fof(f294,plain,(
% 2.11/0.67    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)),
% 2.11/0.67    inference(forward_demodulation,[],[f293,f184])).
% 2.11/0.67  fof(f184,plain,(
% 2.11/0.67    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.11/0.67    inference(resolution,[],[f179,f79])).
% 2.11/0.67  fof(f179,plain,(
% 2.11/0.67    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f178,f72])).
% 2.11/0.67  fof(f72,plain,(
% 2.11/0.67    v1_xboole_0(k1_xboole_0)),
% 2.11/0.67    inference(cnf_transformation,[],[f1])).
% 2.11/0.67  fof(f1,axiom,(
% 2.11/0.67    v1_xboole_0(k1_xboole_0)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.11/0.67  fof(f178,plain,(
% 2.11/0.67    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)) )),
% 2.11/0.67    inference(resolution,[],[f171,f75])).
% 2.11/0.67  fof(f75,plain,(
% 2.11/0.67    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f31])).
% 2.11/0.67  fof(f31,plain,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f20])).
% 2.11/0.67  fof(f20,axiom,(
% 2.11/0.67    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.11/0.67  fof(f171,plain,(
% 2.11/0.67    ( ! [X3] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X3,k2_relat_1(k1_xboole_0))) )),
% 2.11/0.67    inference(resolution,[],[f163,f87])).
% 2.11/0.67  fof(f87,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f56])).
% 2.11/0.67  fof(f56,plain,(
% 2.11/0.67    ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f55])).
% 2.11/0.67  fof(f55,plain,(
% 2.11/0.67    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK4(X1),k1_relat_1(X1)))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f38,plain,(
% 2.11/0.67    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.11/0.67    inference(flattening,[],[f37])).
% 2.11/0.67  fof(f37,plain,(
% 2.11/0.67    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.11/0.67    inference(ennf_transformation,[],[f24])).
% 2.11/0.67  fof(f24,axiom,(
% 2.11/0.67    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 2.11/0.67  fof(f293,plain,(
% 2.11/0.67    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))),
% 2.11/0.67    inference(subsumption_resolution,[],[f292,f70])).
% 2.11/0.67  fof(f292,plain,(
% 2.11/0.67    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) | ~r1_tarski(sK0,sK1)),
% 2.11/0.67    inference(superposition,[],[f243,f113])).
% 2.11/0.67  fof(f243,plain,(
% 2.11/0.67    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 2.11/0.67    inference(resolution,[],[f196,f68])).
% 2.11/0.67  fof(f196,plain,(
% 2.11/0.67    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X1,sK1)))) )),
% 2.11/0.67    inference(resolution,[],[f77,f69])).
% 2.11/0.67  fof(f77,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f33])).
% 2.11/0.67  fof(f33,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f25])).
% 2.11/0.67  fof(f25,axiom,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 2.11/0.67  fof(f208,plain,(
% 2.11/0.67    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 2.11/0.67    inference(superposition,[],[f109,f181])).
% 2.11/0.67  fof(f109,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f80,f107])).
% 2.11/0.67  fof(f80,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f14])).
% 2.11/0.67  fof(f14,axiom,(
% 2.11/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.11/0.67  % SZS output end Proof for theBenchmark
% 2.11/0.67  % (8653)------------------------------
% 2.11/0.67  % (8653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.67  % (8653)Termination reason: Refutation
% 2.11/0.67  
% 2.11/0.67  % (8653)Memory used [KB]: 7419
% 2.11/0.67  % (8653)Time elapsed: 0.231 s
% 2.11/0.67  % (8653)------------------------------
% 2.11/0.67  % (8653)------------------------------
% 2.11/0.67  % (8630)Success in time 0.304 s
%------------------------------------------------------------------------------
