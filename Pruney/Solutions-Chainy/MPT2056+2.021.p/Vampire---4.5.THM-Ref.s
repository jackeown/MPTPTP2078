%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:25 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 354 expanded)
%              Number of leaves         :   21 ( 103 expanded)
%              Depth                    :   21
%              Number of atoms          :  359 (1737 expanded)
%              Number of equality atoms :   52 ( 199 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f519,plain,(
    $false ),
    inference(subsumption_resolution,[],[f518,f56])).

fof(f56,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f518,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f517,f249])).

fof(f249,plain,(
    sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f242,f115])).

fof(f115,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f111,f59])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f66,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f104,f58])).

fof(f58,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = k3_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f100,f94])).

fof(f94,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k3_xboole_0(X4,X5),X6)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f75,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f75,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f242,plain,(
    k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f66,f229])).

fof(f229,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f228,f149])).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(k1_tarski(X4),X3)
      | k1_xboole_0 = k3_xboole_0(X3,k1_tarski(X4)) ) ),
    inference(resolution,[],[f108,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f108,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f104,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f228,plain,(
    r1_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    inference(subsumption_resolution,[],[f221,f117])).

fof(f117,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f114,f58])).

fof(f114,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r1_xboole_0(X4,k1_xboole_0) ) ),
    inference(superposition,[],[f68,f107])).

fof(f221,plain,
    ( r2_hidden(sK3(k1_tarski(k1_xboole_0),sK1),k1_xboole_0)
    | r1_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    inference(superposition,[],[f67,f219])).

fof(f219,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    inference(subsumption_resolution,[],[f218,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f218,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f212,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f210,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f210,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    inference(resolution,[],[f208,f110])).

fof(f110,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X4),X5) ) ),
    inference(resolution,[],[f104,f69])).

fof(f208,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f207,f57])).

fof(f207,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f206,f53])).

fof(f53,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f205,f54])).

fof(f54,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f205,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f204,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f36])).

fof(f204,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f61,f64])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f517,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f516,f199])).

fof(f199,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f516,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f515,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f515,plain,
    ( v1_xboole_0(sK1)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f514,f53])).

fof(f514,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f513,f55])).

fof(f513,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f320,f54])).

fof(f320,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f319,f49])).

fof(f319,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f63,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (3107)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (3088)Refutation not found, incomplete strategy% (3088)------------------------------
% (3088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3088)Termination reason: Refutation not found, incomplete strategy

% (3088)Memory used [KB]: 6268
% (3088)Time elapsed: 0.157 s
% (3088)------------------------------
% (3088)------------------------------
% (3104)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (3086)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (3086)Refutation not found, incomplete strategy% (3086)------------------------------
% 0.22/0.50  % (3086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3102)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (3094)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (3086)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3086)Memory used [KB]: 10746
% 0.22/0.51  % (3086)Time elapsed: 0.094 s
% 0.22/0.51  % (3086)------------------------------
% 0.22/0.51  % (3086)------------------------------
% 0.22/0.51  % (3091)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (3094)Refutation not found, incomplete strategy% (3094)------------------------------
% 0.22/0.51  % (3094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3094)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3094)Memory used [KB]: 10746
% 0.22/0.51  % (3094)Time elapsed: 0.100 s
% 0.22/0.51  % (3094)------------------------------
% 0.22/0.51  % (3094)------------------------------
% 0.22/0.53  % (3093)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (3085)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (3098)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (3087)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (3101)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.54  % (3090)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.54  % (3088)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.54  % (3093)Refutation not found, incomplete strategy% (3093)------------------------------
% 1.23/0.54  % (3093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (3084)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.54  % (3105)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.54  % (3108)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.23/0.54  % (3111)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.23/0.54  % (3110)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.23/0.54  % (3101)Refutation not found, incomplete strategy% (3101)------------------------------
% 1.23/0.54  % (3101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (3097)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.55  % (3101)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (3101)Memory used [KB]: 10746
% 1.23/0.55  % (3101)Time elapsed: 0.130 s
% 1.23/0.55  % (3101)------------------------------
% 1.23/0.55  % (3101)------------------------------
% 1.23/0.55  % (3093)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (3093)Memory used [KB]: 10874
% 1.23/0.55  % (3093)Time elapsed: 0.117 s
% 1.23/0.55  % (3093)------------------------------
% 1.23/0.55  % (3093)------------------------------
% 1.23/0.55  % (3100)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.55  % (3113)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.55  % (3106)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.55  % (3106)Refutation not found, incomplete strategy% (3106)------------------------------
% 1.51/0.55  % (3106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (3106)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (3106)Memory used [KB]: 10746
% 1.51/0.55  % (3106)Time elapsed: 0.143 s
% 1.51/0.55  % (3106)------------------------------
% 1.51/0.55  % (3106)------------------------------
% 1.51/0.56  % (3092)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.56  % (3089)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.56  % (3103)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.56  % (3091)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f519,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(subsumption_resolution,[],[f518,f56])).
% 1.51/0.56  fof(f56,plain,(
% 1.51/0.56    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f35,f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,negated_conjecture,(
% 1.51/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.51/0.56    inference(negated_conjecture,[],[f17])).
% 1.51/0.56  fof(f17,conjecture,(
% 1.51/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 1.51/0.56  fof(f518,plain,(
% 1.51/0.56    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.51/0.56    inference(forward_demodulation,[],[f517,f249])).
% 1.51/0.56  fof(f249,plain,(
% 1.51/0.56    sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(forward_demodulation,[],[f242,f115])).
% 1.51/0.56  fof(f115,plain,(
% 1.51/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.56    inference(forward_demodulation,[],[f111,f59])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.51/0.56  fof(f111,plain,(
% 1.51/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(superposition,[],[f66,f107])).
% 1.51/0.56  fof(f107,plain,(
% 1.51/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(resolution,[],[f104,f58])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.51/0.56  fof(f104,plain,(
% 1.51/0.56    ( ! [X2,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = k3_xboole_0(X1,X2)) )),
% 1.51/0.56    inference(resolution,[],[f100,f94])).
% 1.51/0.56  fof(f94,plain,(
% 1.51/0.56    ( ! [X6,X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X6) | ~r1_xboole_0(X4,X5)) )),
% 1.51/0.56    inference(resolution,[],[f75,f68])).
% 1.51/0.56  fof(f68,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f42])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f41])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(ennf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(rectify,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.51/0.56  fof(f75,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f48])).
% 1.51/0.56  fof(f48,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(rectify,[],[f45])).
% 1.51/0.56  fof(f45,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(nnf_transformation,[],[f31])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.56  fof(f100,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.51/0.56    inference(resolution,[],[f97,f57])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    inference(cnf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.56  fof(f97,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(resolution,[],[f73,f93])).
% 1.51/0.56  fof(f93,plain,(
% 1.51/0.56    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_xboole_0(X2)) )),
% 1.51/0.56    inference(resolution,[],[f75,f64])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.56    inference(rectify,[],[f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.56    inference(nnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.51/0.56  fof(f73,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f44])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.56    inference(flattening,[],[f43])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.56    inference(nnf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.56  fof(f242,plain,(
% 1.51/0.56    k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.51/0.56    inference(superposition,[],[f66,f229])).
% 1.51/0.56  fof(f229,plain,(
% 1.51/0.56    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(resolution,[],[f228,f149])).
% 1.51/0.56  fof(f149,plain,(
% 1.51/0.56    ( ! [X4,X3] : (~r1_xboole_0(k1_tarski(X4),X3) | k1_xboole_0 = k3_xboole_0(X3,k1_tarski(X4))) )),
% 1.51/0.56    inference(resolution,[],[f108,f77])).
% 1.51/0.56  fof(f77,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f32])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.51/0.56  fof(f108,plain,(
% 1.51/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X2))) )),
% 1.51/0.56    inference(resolution,[],[f104,f85])).
% 1.51/0.56  fof(f85,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,k1_tarski(X0)) | r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(resolution,[],[f69,f70])).
% 1.51/0.56  fof(f70,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.51/0.56  fof(f228,plain,(
% 1.51/0.56    r1_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 1.51/0.56    inference(subsumption_resolution,[],[f221,f117])).
% 1.51/0.56  fof(f117,plain,(
% 1.51/0.56    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f114,f58])).
% 1.51/0.56  fof(f114,plain,(
% 1.51/0.56    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r1_xboole_0(X4,k1_xboole_0)) )),
% 1.51/0.56    inference(superposition,[],[f68,f107])).
% 1.51/0.56  fof(f221,plain,(
% 1.51/0.56    r2_hidden(sK3(k1_tarski(k1_xboole_0),sK1),k1_xboole_0) | r1_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 1.51/0.56    inference(superposition,[],[f67,f219])).
% 1.51/0.56  fof(f219,plain,(
% 1.51/0.56    k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 1.51/0.56    inference(subsumption_resolution,[],[f218,f49])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ~v2_struct_0(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f218,plain,(
% 1.51/0.56    k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1) | v2_struct_0(sK0)),
% 1.51/0.56    inference(subsumption_resolution,[],[f212,f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    l1_struct_0(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f212,plain,(
% 1.51/0.56    k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.51/0.56    inference(resolution,[],[f210,f62])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.51/0.56  fof(f210,plain,(
% 1.51/0.56    v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 1.51/0.56    inference(resolution,[],[f208,f110])).
% 1.51/0.56  fof(f110,plain,(
% 1.51/0.56    ( ! [X4,X5] : (r2_hidden(X4,X5) | k1_xboole_0 = k3_xboole_0(k1_tarski(X4),X5)) )),
% 1.51/0.56    inference(resolution,[],[f104,f69])).
% 1.51/0.56  fof(f208,plain,(
% 1.51/0.56    ~r2_hidden(k1_xboole_0,sK1) | v1_xboole_0(k2_struct_0(sK0))),
% 1.51/0.56    inference(resolution,[],[f207,f57])).
% 1.51/0.56  fof(f207,plain,(
% 1.51/0.56    ( ! [X0] : (~v1_xboole_0(X0) | ~r2_hidden(X0,sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f206,f53])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f206,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f205,f54])).
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f205,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f204,f55])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f204,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.56    inference(resolution,[],[f81,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_xboole_0(X2) | v1_xboole_0(X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f61,f64])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.51/0.56    inference(flattening,[],[f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f16])).
% 1.51/0.56  fof(f16,axiom,(
% 1.51/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f42])).
% 1.51/0.56  fof(f517,plain,(
% 1.51/0.56    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(forward_demodulation,[],[f516,f199])).
% 1.51/0.56  fof(f199,plain,(
% 1.51/0.56    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 1.51/0.56    inference(resolution,[],[f78,f55])).
% 1.51/0.56  fof(f78,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f12])).
% 1.51/0.56  fof(f12,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.51/0.56  fof(f516,plain,(
% 1.51/0.56    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(subsumption_resolution,[],[f515,f51])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ~v1_xboole_0(sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f515,plain,(
% 1.51/0.56    v1_xboole_0(sK1) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(subsumption_resolution,[],[f514,f53])).
% 1.51/0.56  fof(f514,plain,(
% 1.51/0.56    ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(subsumption_resolution,[],[f513,f55])).
% 1.51/0.56  fof(f513,plain,(
% 1.51/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.56    inference(resolution,[],[f320,f54])).
% 1.51/0.56  fof(f320,plain,(
% 1.51/0.56    ( ! [X0] : (~v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X0) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f319,f49])).
% 1.51/0.56  fof(f319,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X0) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) | v2_struct_0(sK0)) )),
% 1.51/0.56    inference(resolution,[],[f63,f50])).
% 1.51/0.56  fof(f63,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f27])).
% 1.51/0.56  % (3107)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.57  % (3088)Refutation not found, incomplete strategy% (3088)------------------------------
% 1.51/0.57  % (3088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (3088)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (3088)Memory used [KB]: 6268
% 1.51/0.57  % (3088)Time elapsed: 0.157 s
% 1.51/0.57  % (3088)------------------------------
% 1.51/0.57  % (3088)------------------------------
% 1.51/0.57  % (3104)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f15])).
% 1.51/0.57  fof(f15,axiom,(
% 1.51/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (3091)------------------------------
% 1.51/0.57  % (3091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (3091)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (3091)Memory used [KB]: 6652
% 1.51/0.57  % (3091)Time elapsed: 0.143 s
% 1.51/0.57  % (3091)------------------------------
% 1.51/0.57  % (3091)------------------------------
% 1.51/0.57  % (3083)Success in time 0.208 s
%------------------------------------------------------------------------------
