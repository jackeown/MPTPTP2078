%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 709 expanded)
%              Number of leaves         :   20 ( 220 expanded)
%              Depth                    :   24
%              Number of atoms          :  341 (1572 expanded)
%              Number of equality atoms :   73 ( 641 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f145,f76])).

fof(f76,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f41,f39,f70,f39])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (25727)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f145,plain,(
    o_0_0_xboole_0 != k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)))))) ),
    inference(resolution,[],[f144,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f58,f70,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f144,plain,(
    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),o_0_0_xboole_0) ),
    inference(resolution,[],[f143,f131])).

fof(f131,plain,(
    m2_orders_2(o_0_0_xboole_0,sK0,sK1) ),
    inference(backward_demodulation,[],[f107,f128])).

fof(f128,plain,(
    o_0_0_xboole_0 = sK4(sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f73])).

fof(f73,plain,(
    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f127,plain,
    ( o_0_0_xboole_0 = sK4(sK0,sK1)
    | o_0_0_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f124,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 != k3_tarski(X0) ) ),
    inference(definition_unfolding,[],[f47,f39,f39])).

fof(f47,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 != k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(f124,plain,(
    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f123,f107])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | r2_hidden(X0,k4_orders_2(sK0,sK1)) ) ),
    inference(resolution,[],[f122,f90])).

fof(f90,plain,(
    m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(backward_demodulation,[],[f74,f75])).

fof(f75,plain,(
    k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f40,f39,f71,f39])).

fof(f40,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f74,plain,(
    m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(definition_unfolding,[],[f32,f72])).

fof(f72,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X0),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f42,f71,f39])).

fof(f42,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f44,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_orders_1)).

fof(f32,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f121,f37])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f120,f36])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f119,f35])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f118,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(forward_demodulation,[],[f89,f75])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f49,f72])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

% (25718)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(f107,plain,(
    m2_orders_2(sK4(sK0,sK1),sK0,sK1) ),
    inference(resolution,[],[f106,f90])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | m2_orders_2(sK4(sK0,X0),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | m2_orders_2(sK4(sK0,X0),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | m2_orders_2(sK4(sK0,X0),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | m2_orders_2(sK4(sK0,X0),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f102,f34])).

fof(f102,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | m2_orders_2(sK4(sK0,X0),sK0,X0) ) ),
    inference(resolution,[],[f96,f38])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f143,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f142,f90])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f141,f37])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f140,f36])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f139,f35])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(resolution,[],[f91,f38])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(o_0_0_xboole_0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(forward_demodulation,[],[f80,f75])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:54:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (25719)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (25719)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (25735)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f41,f39,f70,f39])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f55,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f53,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f54,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f59,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f60,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f61,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f62,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  % (25727)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    o_0_0_xboole_0 != k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0)),k1_funct_1(sK1,u1_struct_0(sK0))))))),
% 0.22/0.52    inference(resolution,[],[f144,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f58,f70,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f43,f68])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),o_0_0_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f143,f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    m2_orders_2(o_0_0_xboole_0,sK0,sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f107,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    o_0_0_xboole_0 = sK4(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.52    inference(definition_unfolding,[],[f33,f39])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f20])).
% 0.22/0.52  fof(f20,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    o_0_0_xboole_0 = sK4(sK0,sK1) | o_0_0_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f124,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 != k3_tarski(X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f47,f39,f39])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,axiom,(
% 0.22/0.52    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f123,f107])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f122,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f74,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0)),
% 0.22/0.52    inference(definition_unfolding,[],[f40,f39,f71,f39])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))),
% 0.22/0.52    inference(definition_unfolding,[],[f32,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X0),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f44,f42,f71,f39])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (k9_setfam_1(X0) = k1_zfmisc_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_orders_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f121,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f120,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f119,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v3_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.52    inference(resolution,[],[f95,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f89,f75])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f49,f72])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  % (25718)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    m2_orders_2(sK4(sK0,sK1),sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f106,f90])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | m2_orders_2(sK4(sK0,X0),sK0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f105,f37])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X0] : (~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | m2_orders_2(sK4(sK0,X0),sK0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f36])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | m2_orders_2(sK4(sK0,X0),sK0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f103,f35])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | m2_orders_2(sK4(sK0,X0),sK0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f102,f34])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | m2_orders_2(sK4(sK0,X0),sK0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f96,f38])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(o_0_0_xboole_0))) | m2_orders_2(sK4(X0,X1),X0,X1)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f85,f75])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | m2_orders_2(sK4(X0,X1),X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f56,f72])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK4(X0,X1),X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) )),
% 0.22/0.52    inference(resolution,[],[f142,f90])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f37])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f36])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f139,f35])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f138,f34])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.52    inference(resolution,[],[f91,f38])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(o_0_0_xboole_0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f80,f75])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f48,f72])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25719)------------------------------
% 0.22/0.52  % (25719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25719)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25719)Memory used [KB]: 6268
% 0.22/0.52  % (25719)Time elapsed: 0.089 s
% 0.22/0.52  % (25719)------------------------------
% 0.22/0.52  % (25719)------------------------------
% 0.22/0.52  % (25712)Success in time 0.155 s
%------------------------------------------------------------------------------
