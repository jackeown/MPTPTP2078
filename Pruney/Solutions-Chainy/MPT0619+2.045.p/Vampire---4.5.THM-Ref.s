%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 474 expanded)
%              Number of leaves         :   12 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          :  209 (1173 expanded)
%              Number of equality atoms :  109 ( 717 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(resolution,[],[f274,f109])).

fof(f109,plain,(
    sP3(k1_funct_1(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f101,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f101,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f81,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK0,sK0,sK0,sK0,sK0)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f76,f63])).

fof(f63,plain,(
    k1_relat_1(sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

% (7639)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X3,X4))
      | ~ sP7(X6,X4,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ sP7(X6,X4,X3,X2,X1,X0)
      | r2_hidden(X6,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ sP7(X6,X4,X3,X2,X1,X0)
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f81,plain,(
    ! [X6,X4,X2,X3,X1] : sP7(X6,X4,X3,X2,X1,X6) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X0 != X6
      | sP7(X6,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f274,plain,(
    ! [X2] : ~ sP3(X2,sK1) ),
    inference(global_subsumption,[],[f82,f270])).

fof(f270,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ sP3(X2,sK1) ) ),
    inference(backward_demodulation,[],[f189,f250])).

fof(f250,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f109,f249])).

fof(f249,plain,(
    ! [X4] :
      ( k1_xboole_0 = k2_relat_1(sK1)
      | ~ sP3(X4,sK1) ) ),
    inference(global_subsumption,[],[f62,f182,f243])).

fof(f243,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK0) != X4
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
      | ~ sP3(X4,sK1) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK0) != X4
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
      | k1_xboole_0 = k2_relat_1(sK1)
      | ~ sP3(X4,sK1) ) ),
    inference(superposition,[],[f64,f205])).

fof(f205,plain,(
    ! [X0] :
      ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X0
      | k1_xboole_0 = k2_relat_1(sK1)
      | ~ sP3(X0,sK1) ) ),
    inference(resolution,[],[f149,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,sK1)
      | X0 = X1
      | ~ sP3(X0,sK1) ) ),
    inference(superposition,[],[f182,f182])).

fof(f149,plain,
    ( sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1)
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(global_subsumption,[],[f23,f22,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f147,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f147,plain,
    ( r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X1] :
      ( k2_relat_1(sK1) != X1
      | k1_xboole_0 = X1
      | r2_hidden(sK5(X1,k1_funct_1(sK1,sK0)),X1) ) ),
    inference(superposition,[],[f62,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f182,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = X0
      | ~ sP3(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = X0
      | ~ sP3(X0,sK1)
      | ~ sP3(X0,sK1) ) ),
    inference(superposition,[],[f31,f175])).

fof(f175,plain,(
    ! [X0] :
      ( sK0 = sK4(sK1,X0)
      | ~ sP3(X0,sK1) ) ),
    inference(resolution,[],[f170,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f170,plain,(
    ! [X25] :
      ( ~ r2_hidden(X25,k1_relat_1(sK1))
      | sK0 = X25 ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X25] :
      ( sK0 = X25
      | sK0 = X25
      | sK0 = X25
      | sK0 = X25
      | sK0 = X25
      | ~ r2_hidden(X25,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f52,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP7(X0,sK0,sK0,sK0,sK0,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f75,f63])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X3,X4))
      | sP7(X6,X4,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP7(X6,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X6,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP7(X6,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP7(X6,X4,X3,X2,X1,X0)
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | X4 = X6
      | X0 = X6 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    k2_relat_1(sK1) != k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f25,f61])).

fof(f25,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f189,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_relat_1(sK1))
      | ~ sP3(X2,sK1) ) ),
    inference(superposition,[],[f110,f182])).

fof(f110,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f109,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:11:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (7624)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (7619)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.50  % (7632)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (7635)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (7643)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (7627)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (7626)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.09/0.52  % (7621)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.09/0.52  % (7640)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.09/0.52  % (7647)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.09/0.52  % (7625)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.09/0.52  % (7646)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.09/0.52  % (7618)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.09/0.52  % (7637)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.09/0.52  % (7631)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.09/0.52  % (7622)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.09/0.52  % (7634)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.09/0.53  % (7629)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.09/0.53  % (7644)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.19/0.53  % (7635)Refutation not found, incomplete strategy% (7635)------------------------------
% 1.19/0.53  % (7635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (7628)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.19/0.53  % (7645)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.19/0.53  % (7641)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.19/0.53  % (7636)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.19/0.53  % (7638)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.53  % (7630)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (7623)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.54  % (7633)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.54  % (7620)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.54  % (7635)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.54  
% 1.19/0.54  % (7635)Memory used [KB]: 10618
% 1.19/0.54  % (7635)Time elapsed: 0.120 s
% 1.19/0.54  % (7635)------------------------------
% 1.19/0.54  % (7635)------------------------------
% 1.19/0.54  % (7642)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.19/0.55  % (7642)Refutation found. Thanks to Tanya!
% 1.19/0.55  % SZS status Theorem for theBenchmark
% 1.19/0.55  % SZS output start Proof for theBenchmark
% 1.19/0.55  fof(f280,plain,(
% 1.19/0.55    $false),
% 1.19/0.55    inference(resolution,[],[f274,f109])).
% 1.19/0.55  fof(f109,plain,(
% 1.19/0.55    sP3(k1_funct_1(sK1,sK0),sK1)),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f101,f72])).
% 1.19/0.55  fof(f72,plain,(
% 1.19/0.55    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.19/0.55    inference(equality_resolution,[],[f29])).
% 1.19/0.55  fof(f29,plain,(
% 1.19/0.55    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f19])).
% 1.19/0.55  fof(f19,plain,(
% 1.19/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.55    inference(flattening,[],[f18])).
% 1.19/0.55  fof(f18,plain,(
% 1.19/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.19/0.55    inference(ennf_transformation,[],[f12])).
% 1.19/0.55  fof(f12,axiom,(
% 1.19/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.19/0.55  fof(f101,plain,(
% 1.19/0.55    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f81,f96])).
% 1.19/0.55  fof(f96,plain,(
% 1.19/0.55    ( ! [X0] : (~sP7(X0,sK0,sK0,sK0,sK0,sK0) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.19/0.55    inference(superposition,[],[f76,f63])).
% 1.19/0.55  fof(f63,plain,(
% 1.19/0.55    k1_relat_1(sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.19/0.55    inference(definition_unfolding,[],[f24,f61])).
% 1.19/0.55  fof(f61,plain,(
% 1.19/0.55    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.19/0.55    inference(definition_unfolding,[],[f26,f60])).
% 1.19/0.55  fof(f60,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.19/0.55    inference(definition_unfolding,[],[f37,f59])).
% 1.19/0.55  fof(f59,plain,(
% 1.19/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.19/0.55    inference(definition_unfolding,[],[f43,f58])).
% 1.19/0.55  fof(f58,plain,(
% 1.19/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.19/0.55    inference(definition_unfolding,[],[f44,f57])).
% 1.19/0.55  fof(f57,plain,(
% 1.19/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.19/0.55    inference(definition_unfolding,[],[f45,f46])).
% 1.19/0.55  fof(f46,plain,(
% 1.19/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f6])).
% 1.19/0.55  fof(f6,axiom,(
% 1.19/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.19/0.55  fof(f45,plain,(
% 1.19/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f5])).
% 1.19/0.55  fof(f5,axiom,(
% 1.19/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.19/0.55  fof(f44,plain,(
% 1.19/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f4])).
% 1.19/0.55  fof(f4,axiom,(
% 1.19/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.19/0.55  fof(f43,plain,(
% 1.19/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f3])).
% 1.19/0.55  fof(f3,axiom,(
% 1.19/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.19/0.55  % (7639)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.19/0.55  fof(f37,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f2])).
% 1.19/0.55  fof(f2,axiom,(
% 1.19/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.19/0.55  fof(f26,plain,(
% 1.19/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f1])).
% 1.19/0.55  fof(f1,axiom,(
% 1.19/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.55  fof(f24,plain,(
% 1.19/0.55    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.19/0.55    inference(cnf_transformation,[],[f16])).
% 1.19/0.55  fof(f16,plain,(
% 1.19/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.19/0.55    inference(flattening,[],[f15])).
% 1.19/0.55  fof(f15,plain,(
% 1.19/0.55    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.19/0.55    inference(ennf_transformation,[],[f14])).
% 1.19/0.55  fof(f14,negated_conjecture,(
% 1.19/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.19/0.55    inference(negated_conjecture,[],[f13])).
% 1.19/0.55  fof(f13,conjecture,(
% 1.19/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.19/0.55  fof(f76,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) | ~sP7(X6,X4,X3,X2,X1,X0)) )),
% 1.19/0.55    inference(equality_resolution,[],[f69])).
% 1.19/0.55  fof(f69,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~sP7(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.19/0.55    inference(definition_unfolding,[],[f53,f57])).
% 1.19/0.55  fof(f53,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~sP7(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.19/0.55    inference(cnf_transformation,[],[f21])).
% 1.19/0.55  fof(f21,plain,(
% 1.19/0.55    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.19/0.55    inference(ennf_transformation,[],[f10])).
% 1.19/0.55  fof(f10,axiom,(
% 1.19/0.55    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.19/0.55  fof(f81,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X3,X1] : (sP7(X6,X4,X3,X2,X1,X6)) )),
% 1.19/0.55    inference(equality_resolution,[],[f47])).
% 1.19/0.55  fof(f47,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (X0 != X6 | sP7(X6,X4,X3,X2,X1,X0)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f21])).
% 1.19/0.55  fof(f274,plain,(
% 1.19/0.55    ( ! [X2] : (~sP3(X2,sK1)) )),
% 1.19/0.55    inference(global_subsumption,[],[f82,f270])).
% 1.19/0.55  fof(f270,plain,(
% 1.19/0.55    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~sP3(X2,sK1)) )),
% 1.19/0.55    inference(backward_demodulation,[],[f189,f250])).
% 1.19/0.55  fof(f250,plain,(
% 1.19/0.55    k1_xboole_0 = k2_relat_1(sK1)),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f109,f249])).
% 1.19/0.55  fof(f249,plain,(
% 1.19/0.55    ( ! [X4] : (k1_xboole_0 = k2_relat_1(sK1) | ~sP3(X4,sK1)) )),
% 1.19/0.55    inference(global_subsumption,[],[f62,f182,f243])).
% 1.19/0.55  fof(f243,plain,(
% 1.19/0.55    ( ! [X4] : (k1_funct_1(sK1,sK0) != X4 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | ~sP3(X4,sK1)) )),
% 1.19/0.55    inference(duplicate_literal_removal,[],[f242])).
% 1.19/0.55  fof(f242,plain,(
% 1.19/0.55    ( ! [X4] : (k1_funct_1(sK1,sK0) != X4 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | k1_xboole_0 = k2_relat_1(sK1) | ~sP3(X4,sK1)) )),
% 1.19/0.55    inference(superposition,[],[f64,f205])).
% 1.19/0.55  fof(f205,plain,(
% 1.19/0.55    ( ! [X0] : (sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X0 | k1_xboole_0 = k2_relat_1(sK1) | ~sP3(X0,sK1)) )),
% 1.19/0.55    inference(resolution,[],[f149,f186])).
% 1.19/0.55  fof(f186,plain,(
% 1.19/0.55    ( ! [X0,X1] : (~sP3(X1,sK1) | X0 = X1 | ~sP3(X0,sK1)) )),
% 1.19/0.55    inference(superposition,[],[f182,f182])).
% 1.19/0.55  fof(f149,plain,(
% 1.19/0.55    sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1) | k1_xboole_0 = k2_relat_1(sK1)),
% 1.19/0.55    inference(global_subsumption,[],[f23,f22,f148])).
% 1.19/0.55  fof(f148,plain,(
% 1.19/0.55    k1_xboole_0 = k2_relat_1(sK1) | ~v1_funct_1(sK1) | sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1) | ~v1_relat_1(sK1)),
% 1.19/0.55    inference(resolution,[],[f147,f70])).
% 1.19/0.55  fof(f70,plain,(
% 1.19/0.55    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.19/0.55    inference(equality_resolution,[],[f33])).
% 1.19/0.55  fof(f33,plain,(
% 1.19/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.19/0.55    inference(cnf_transformation,[],[f19])).
% 1.19/0.55  fof(f147,plain,(
% 1.19/0.55    r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1)),
% 1.19/0.55    inference(equality_resolution,[],[f137])).
% 1.19/0.55  fof(f137,plain,(
% 1.19/0.55    ( ! [X1] : (k2_relat_1(sK1) != X1 | k1_xboole_0 = X1 | r2_hidden(sK5(X1,k1_funct_1(sK1,sK0)),X1)) )),
% 1.19/0.55    inference(superposition,[],[f62,f65])).
% 1.19/0.55  fof(f65,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.19/0.55    inference(definition_unfolding,[],[f41,f61])).
% 1.19/0.55  fof(f41,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f20])).
% 1.19/0.55  fof(f20,plain,(
% 1.19/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.19/0.55    inference(ennf_transformation,[],[f9])).
% 1.19/0.55  fof(f9,axiom,(
% 1.19/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.19/0.55  fof(f22,plain,(
% 1.19/0.55    v1_relat_1(sK1)),
% 1.19/0.55    inference(cnf_transformation,[],[f16])).
% 1.19/0.55  fof(f23,plain,(
% 1.19/0.55    v1_funct_1(sK1)),
% 1.19/0.55    inference(cnf_transformation,[],[f16])).
% 1.19/0.55  fof(f64,plain,(
% 1.19/0.55    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.19/0.55    inference(definition_unfolding,[],[f42,f61])).
% 1.19/0.55  fof(f42,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 1.19/0.55    inference(cnf_transformation,[],[f20])).
% 1.19/0.55  fof(f182,plain,(
% 1.19/0.55    ( ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~sP3(X0,sK1)) )),
% 1.19/0.55    inference(duplicate_literal_removal,[],[f179])).
% 1.19/0.55  fof(f179,plain,(
% 1.19/0.55    ( ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~sP3(X0,sK1) | ~sP3(X0,sK1)) )),
% 1.19/0.55    inference(superposition,[],[f31,f175])).
% 1.19/0.55  fof(f175,plain,(
% 1.19/0.55    ( ! [X0] : (sK0 = sK4(sK1,X0) | ~sP3(X0,sK1)) )),
% 1.19/0.55    inference(resolution,[],[f170,f30])).
% 1.19/0.55  fof(f30,plain,(
% 1.19/0.55    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f19])).
% 1.19/0.55  fof(f170,plain,(
% 1.19/0.55    ( ! [X25] : (~r2_hidden(X25,k1_relat_1(sK1)) | sK0 = X25) )),
% 1.19/0.55    inference(duplicate_literal_removal,[],[f167])).
% 1.19/0.55  fof(f167,plain,(
% 1.19/0.55    ( ! [X25] : (sK0 = X25 | sK0 = X25 | sK0 = X25 | sK0 = X25 | sK0 = X25 | ~r2_hidden(X25,k1_relat_1(sK1))) )),
% 1.19/0.55    inference(resolution,[],[f52,f89])).
% 1.19/0.55  fof(f89,plain,(
% 1.19/0.55    ( ! [X0] : (sP7(X0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.19/0.55    inference(superposition,[],[f75,f63])).
% 1.19/0.55  fof(f75,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (~r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) | sP7(X6,X4,X3,X2,X1,X0)) )),
% 1.19/0.55    inference(equality_resolution,[],[f68])).
% 1.19/0.55  fof(f68,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP7(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.19/0.55    inference(definition_unfolding,[],[f54,f57])).
% 1.19/0.55  fof(f54,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP7(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.19/0.55    inference(cnf_transformation,[],[f21])).
% 1.19/0.55  fof(f52,plain,(
% 1.19/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (~sP7(X6,X4,X3,X2,X1,X0) | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | X0 = X6) )),
% 1.19/0.55    inference(cnf_transformation,[],[f21])).
% 1.19/0.55  fof(f31,plain,(
% 1.19/0.55    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f19])).
% 1.19/0.55  fof(f62,plain,(
% 1.19/0.55    k2_relat_1(sK1) != k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.19/0.55    inference(definition_unfolding,[],[f25,f61])).
% 1.19/0.55  fof(f25,plain,(
% 1.19/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.19/0.55    inference(cnf_transformation,[],[f16])).
% 1.19/0.55  fof(f189,plain,(
% 1.19/0.55    ( ! [X2] : (r2_hidden(X2,k2_relat_1(sK1)) | ~sP3(X2,sK1)) )),
% 1.19/0.55    inference(superposition,[],[f110,f182])).
% 1.19/0.55  fof(f110,plain,(
% 1.19/0.55    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f22,f23,f109,f71])).
% 1.19/0.55  fof(f71,plain,(
% 1.19/0.55    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.19/0.55    inference(equality_resolution,[],[f32])).
% 1.19/0.55  fof(f32,plain,(
% 1.19/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP3(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.19/0.55    inference(cnf_transformation,[],[f19])).
% 1.19/0.55  fof(f82,plain,(
% 1.19/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.19/0.55    inference(superposition,[],[f36,f73])).
% 1.19/0.55  fof(f73,plain,(
% 1.19/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.19/0.55    inference(equality_resolution,[],[f40])).
% 1.19/0.55  fof(f40,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.19/0.55    inference(cnf_transformation,[],[f7])).
% 1.19/0.55  fof(f7,axiom,(
% 1.19/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.19/0.55  fof(f36,plain,(
% 1.19/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.19/0.55    inference(cnf_transformation,[],[f8])).
% 1.19/0.55  fof(f8,axiom,(
% 1.19/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.19/0.55  % SZS output end Proof for theBenchmark
% 1.19/0.55  % (7642)------------------------------
% 1.19/0.55  % (7642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.55  % (7642)Termination reason: Refutation
% 1.19/0.55  
% 1.19/0.55  % (7642)Memory used [KB]: 6396
% 1.19/0.55  % (7642)Time elapsed: 0.133 s
% 1.19/0.55  % (7642)------------------------------
% 1.19/0.55  % (7642)------------------------------
% 1.19/0.55  % (7617)Success in time 0.178 s
%------------------------------------------------------------------------------
