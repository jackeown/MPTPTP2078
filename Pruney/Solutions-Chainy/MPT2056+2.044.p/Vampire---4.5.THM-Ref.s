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
% DateTime   : Thu Dec  3 13:23:28 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  110 (1200 expanded)
%              Number of leaves         :   17 ( 302 expanded)
%              Depth                    :   21
%              Number of atoms          :  271 (4018 expanded)
%              Number of equality atoms :   56 ( 771 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f963,plain,(
    $false ),
    inference(global_subsumption,[],[f42,f954])).

fof(f954,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f758,f939])).

fof(f939,plain,(
    k1_xboole_0 = sK3(sK1,k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f762,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f57,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
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

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f762,plain,(
    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f755,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f755,plain,(
    ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f754])).

fof(f754,plain,
    ( sK1 != sK1
    | ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f736,f389])).

fof(f389,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f73,f385])).

fof(f385,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f383,f384])).

fof(f384,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),k3_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),X0)) ),
    inference(forward_demodulation,[],[f357,f372])).

fof(f372,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) = k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f361,f360])).

fof(f360,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X0)) ),
    inference(unit_resulting_resolution,[],[f117,f177,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f177,plain,(
    ! [X0,X1] : ~ sP5(X0,X1,k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f121,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f121,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f114,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f114,plain,(
    r1_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f57])).

fof(f39,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))))) ),
    inference(unit_resulting_resolution,[],[f113,f52])).

fof(f113,plain,(
    r1_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) ),
    inference(unit_resulting_resolution,[],[f39,f57])).

fof(f361,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)) = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X0)) ),
    inference(unit_resulting_resolution,[],[f121,f177,f78])).

fof(f357,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X0)) ),
    inference(unit_resulting_resolution,[],[f84,f177,f78])).

fof(f84,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f43,f58])).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f383,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),k3_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),X1)) ),
    inference(forward_demodulation,[],[f358,f372])).

fof(f358,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X1)) ),
    inference(unit_resulting_resolution,[],[f87,f177,f78])).

fof(f87,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f43,f52])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f736,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f627,f704])).

fof(f704,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f487,f52])).

fof(f487,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X9,X10),X10)
      | k1_xboole_0 = X10 ) ),
    inference(forward_demodulation,[],[f486,f389])).

fof(f486,plain,(
    ! [X10,X9] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X10
      | r2_hidden(sK4(k1_xboole_0,X9,X10),X10) ) ),
    inference(forward_demodulation,[],[f366,f245])).

fof(f245,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f238,f73])).

fof(f238,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f67,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f50,f51,f51])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f366,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X9,X10),X10)
      | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = X10 ) ),
    inference(resolution,[],[f78,f86])).

fof(f86,plain,(
    ! [X0,X1] : ~ sP5(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f84,f61])).

fof(f627,plain,(
    sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) ),
    inference(superposition,[],[f39,f553])).

fof(f553,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f546,f281])).

fof(f281,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f59,plain,(
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

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f46,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f22])).

fof(f546,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f34,f69,f70,f68,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f46,f46,f46,f46])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

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

fof(f70,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f36,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f37,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f758,plain,(
    ~ v1_xboole_0(sK3(sK1,k1_tarski(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f755,f570])).

fof(f570,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK1,X0))
      | r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f523,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f523,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f69,f70,f71,f34,f83,f522])).

fof(f522,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f74,f68])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(definition_unfolding,[],[f47,f46,f46,f46,f46])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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

fof(f83,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f71,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f35,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (25251)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (25267)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (25259)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (25244)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (25241)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (25250)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (25243)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (25239)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (25261)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25259)Refutation not found, incomplete strategy% (25259)------------------------------
% 0.21/0.52  % (25259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25253)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (25259)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25259)Memory used [KB]: 10746
% 0.21/0.52  % (25259)Time elapsed: 0.111 s
% 0.21/0.52  % (25259)------------------------------
% 0.21/0.52  % (25259)------------------------------
% 0.21/0.52  % (25249)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (25240)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (25247)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (25264)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (25238)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (25254)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (25242)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (25268)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (25262)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (25265)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (25257)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (25261)Refutation not found, incomplete strategy% (25261)------------------------------
% 0.21/0.54  % (25261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25261)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25261)Memory used [KB]: 10746
% 0.21/0.54  % (25261)Time elapsed: 0.125 s
% 0.21/0.54  % (25261)------------------------------
% 0.21/0.54  % (25261)------------------------------
% 0.21/0.54  % (25245)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (25266)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (25256)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (25260)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (25255)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (25260)Refutation not found, incomplete strategy% (25260)------------------------------
% 1.41/0.55  % (25260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (25260)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (25260)Memory used [KB]: 1791
% 1.41/0.55  % (25260)Time elapsed: 0.140 s
% 1.41/0.55  % (25260)------------------------------
% 1.41/0.55  % (25260)------------------------------
% 1.41/0.55  % (25252)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (25246)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (25246)Refutation not found, incomplete strategy% (25246)------------------------------
% 1.41/0.55  % (25246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (25246)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (25246)Memory used [KB]: 10746
% 1.41/0.55  % (25246)Time elapsed: 0.148 s
% 1.41/0.55  % (25246)------------------------------
% 1.41/0.55  % (25246)------------------------------
% 1.41/0.55  % (25258)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (25263)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.61  % (25263)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.61  % SZS output start Proof for theBenchmark
% 1.59/0.61  fof(f963,plain,(
% 1.59/0.61    $false),
% 1.59/0.61    inference(global_subsumption,[],[f42,f954])).
% 1.59/0.61  fof(f954,plain,(
% 1.59/0.61    ~v1_xboole_0(k1_xboole_0)),
% 1.59/0.61    inference(backward_demodulation,[],[f758,f939])).
% 1.59/0.61  fof(f939,plain,(
% 1.59/0.61    k1_xboole_0 = sK3(sK1,k1_tarski(k1_xboole_0))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f762,f115])).
% 1.59/0.61  fof(f115,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 1.59/0.61    inference(resolution,[],[f57,f58])).
% 1.59/0.61  fof(f58,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f32])).
% 1.59/0.61  fof(f32,plain,(
% 1.59/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f10])).
% 1.59/0.61  fof(f10,axiom,(
% 1.59/0.61    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.59/0.61  fof(f57,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.59/0.61    inference(cnf_transformation,[],[f31])).
% 1.59/0.61  fof(f31,plain,(
% 1.59/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.59/0.61    inference(ennf_transformation,[],[f11])).
% 1.59/0.61  fof(f11,axiom,(
% 1.59/0.61    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.59/0.61  fof(f762,plain,(
% 1.59/0.61    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f755,f56])).
% 1.59/0.61  fof(f56,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f30])).
% 1.59/0.61  fof(f30,plain,(
% 1.59/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f20])).
% 1.59/0.61  fof(f20,plain,(
% 1.59/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.61    inference(rectify,[],[f3])).
% 1.59/0.61  fof(f3,axiom,(
% 1.59/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.59/0.61  fof(f755,plain,(
% 1.59/0.61    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.59/0.61    inference(trivial_inequality_removal,[],[f754])).
% 1.59/0.61  fof(f754,plain,(
% 1.59/0.61    sK1 != sK1 | ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.59/0.61    inference(forward_demodulation,[],[f736,f389])).
% 1.59/0.61  fof(f389,plain,(
% 1.59/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.61    inference(backward_demodulation,[],[f73,f385])).
% 1.59/0.61  fof(f385,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.61    inference(backward_demodulation,[],[f383,f384])).
% 1.59/0.61  fof(f384,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),k3_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),X0))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f357,f372])).
% 1.59/0.61  fof(f372,plain,(
% 1.59/0.61    k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) = k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1))),
% 1.59/0.61    inference(backward_demodulation,[],[f361,f360])).
% 1.59/0.61  fof(f360,plain,(
% 1.59/0.61    ( ! [X0] : (k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X0))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f117,f177,f78])).
% 1.59/0.61  fof(f78,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.59/0.61    inference(definition_unfolding,[],[f65,f51])).
% 1.59/0.61  fof(f51,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f5])).
% 1.59/0.61  fof(f5,axiom,(
% 1.59/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.61  fof(f65,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.59/0.61    inference(cnf_transformation,[],[f1])).
% 1.59/0.61  fof(f1,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.59/0.61  fof(f177,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~sP5(X0,X1,k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f121,f61])).
% 1.59/0.61  fof(f61,plain,(
% 1.59/0.61    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f1])).
% 1.59/0.61  fof(f121,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f114,f52])).
% 1.59/0.61  fof(f52,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f29])).
% 1.59/0.61  fof(f29,plain,(
% 1.59/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f19])).
% 1.59/0.61  fof(f19,plain,(
% 1.59/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.61    inference(rectify,[],[f4])).
% 1.59/0.61  fof(f4,axiom,(
% 1.59/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.59/0.61  fof(f114,plain,(
% 1.59/0.61    r1_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f39,f57])).
% 1.59/0.61  fof(f39,plain,(
% 1.59/0.61    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f22,plain,(
% 1.59/0.61    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.59/0.61    inference(flattening,[],[f21])).
% 1.59/0.61  fof(f21,plain,(
% 1.59/0.61    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f18])).
% 1.59/0.61  fof(f18,negated_conjecture,(
% 1.59/0.61    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.59/0.61    inference(negated_conjecture,[],[f17])).
% 1.59/0.61  fof(f17,conjecture,(
% 1.59/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 1.59/0.61  fof(f117,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f113,f52])).
% 1.59/0.61  fof(f113,plain,(
% 1.59/0.61    r1_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f39,f57])).
% 1.59/0.61  fof(f361,plain,(
% 1.59/0.61    ( ! [X0] : (k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)) = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X0))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f121,f177,f78])).
% 1.59/0.61  fof(f357,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X0))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f84,f177,f78])).
% 1.59/0.61  fof(f84,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f43,f58])).
% 1.59/0.61  fof(f43,plain,(
% 1.59/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f9])).
% 1.59/0.61  fof(f9,axiom,(
% 1.59/0.61    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.59/0.61  fof(f383,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),k3_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),X1))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f358,f372])).
% 1.59/0.61  fof(f358,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),k3_xboole_0(k3_xboole_0(k1_tarski(k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),k1_tarski(sK1)),X1))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f87,f177,f78])).
% 1.59/0.61  fof(f87,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f43,f52])).
% 1.59/0.61  fof(f73,plain,(
% 1.59/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.59/0.61    inference(definition_unfolding,[],[f45,f51])).
% 1.59/0.61  fof(f45,plain,(
% 1.59/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.61    inference(cnf_transformation,[],[f6])).
% 1.59/0.61  fof(f6,axiom,(
% 1.59/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.59/0.61  fof(f736,plain,(
% 1.59/0.61    sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.59/0.61    inference(superposition,[],[f627,f704])).
% 1.59/0.61  fof(f704,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.59/0.61    inference(resolution,[],[f487,f52])).
% 1.59/0.61  fof(f487,plain,(
% 1.59/0.61    ( ! [X10,X9] : (r2_hidden(sK4(k1_xboole_0,X9,X10),X10) | k1_xboole_0 = X10) )),
% 1.59/0.61    inference(forward_demodulation,[],[f486,f389])).
% 1.59/0.61  fof(f486,plain,(
% 1.59/0.61    ( ! [X10,X9] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = X10 | r2_hidden(sK4(k1_xboole_0,X9,X10),X10)) )),
% 1.59/0.61    inference(forward_demodulation,[],[f366,f245])).
% 1.59/0.61  fof(f245,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.61    inference(forward_demodulation,[],[f238,f73])).
% 1.59/0.61  fof(f238,plain,(
% 1.59/0.61    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.59/0.61    inference(superposition,[],[f67,f72])).
% 1.59/0.61  fof(f72,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f44,f51])).
% 1.59/0.61  fof(f44,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f8])).
% 1.59/0.61  fof(f8,axiom,(
% 1.59/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.59/0.61  fof(f67,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f50,f51,f51])).
% 1.59/0.61  fof(f50,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f7])).
% 1.59/0.61  fof(f7,axiom,(
% 1.59/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.59/0.61  fof(f366,plain,(
% 1.59/0.61    ( ! [X10,X9] : (r2_hidden(sK4(k1_xboole_0,X9,X10),X10) | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = X10) )),
% 1.59/0.61    inference(resolution,[],[f78,f86])).
% 1.59/0.61  fof(f86,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~sP5(X0,X1,k1_xboole_0)) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f84,f61])).
% 1.59/0.61  fof(f627,plain,(
% 1.59/0.61    sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))),
% 1.59/0.61    inference(superposition,[],[f39,f553])).
% 1.59/0.61  fof(f553,plain,(
% 1.59/0.61    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))),
% 1.59/0.61    inference(forward_demodulation,[],[f546,f281])).
% 1.59/0.61  fof(f281,plain,(
% 1.59/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f68,f76])).
% 1.59/0.61  fof(f76,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f59,f51])).
% 1.59/0.61  fof(f59,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f33])).
% 1.59/0.61  fof(f33,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f12])).
% 1.59/0.61  fof(f12,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.59/0.61  fof(f68,plain,(
% 1.59/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.59/0.61    inference(definition_unfolding,[],[f38,f46])).
% 1.59/0.61  fof(f46,plain,(
% 1.59/0.61    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f14])).
% 1.59/0.61  fof(f14,axiom,(
% 1.59/0.61    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.59/0.61  fof(f38,plain,(
% 1.59/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f546,plain,(
% 1.59/0.61    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f40,f41,f34,f69,f70,f68,f75])).
% 1.59/0.61  fof(f75,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | v2_struct_0(X0)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f49,f46,f46,f46,f46])).
% 1.59/0.61  fof(f49,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f28])).
% 1.59/0.61  fof(f28,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.59/0.61    inference(flattening,[],[f27])).
% 1.59/0.61  fof(f27,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f15])).
% 1.59/0.61  fof(f15,axiom,(
% 1.59/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 1.59/0.61  fof(f70,plain,(
% 1.59/0.61    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.59/0.61    inference(definition_unfolding,[],[f36,f46])).
% 1.59/0.61  fof(f36,plain,(
% 1.59/0.61    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f69,plain,(
% 1.59/0.61    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.59/0.61    inference(definition_unfolding,[],[f37,f46])).
% 1.59/0.61  fof(f37,plain,(
% 1.59/0.61    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f34,plain,(
% 1.59/0.61    ~v1_xboole_0(sK1)),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f41,plain,(
% 1.59/0.61    l1_struct_0(sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f40,plain,(
% 1.59/0.61    ~v2_struct_0(sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f758,plain,(
% 1.59/0.61    ~v1_xboole_0(sK3(sK1,k1_tarski(k1_xboole_0)))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f755,f570])).
% 1.59/0.61  fof(f570,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_xboole_0(sK3(sK1,X0)) | r1_xboole_0(sK1,X0)) )),
% 1.59/0.61    inference(resolution,[],[f523,f55])).
% 1.59/0.61  fof(f55,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f30])).
% 1.59/0.61  fof(f523,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) )),
% 1.59/0.61    inference(global_subsumption,[],[f69,f70,f71,f34,f83,f522])).
% 1.59/0.61  fof(f522,plain,(
% 1.59/0.61    ( ! [X0] : (v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) )),
% 1.59/0.61    inference(resolution,[],[f74,f68])).
% 1.59/0.61  fof(f74,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f47,f46,f46,f46,f46])).
% 1.59/0.61  fof(f47,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f24])).
% 1.59/0.61  fof(f24,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.59/0.61    inference(flattening,[],[f23])).
% 1.59/0.61  fof(f23,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f16])).
% 1.59/0.61  fof(f16,axiom,(
% 1.59/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 1.59/0.61  fof(f83,plain,(
% 1.59/0.61    ~v1_xboole_0(k2_struct_0(sK0))),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f40,f41,f48])).
% 1.59/0.61  fof(f48,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f26])).
% 1.59/0.61  fof(f26,plain,(
% 1.59/0.61    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.59/0.61    inference(flattening,[],[f25])).
% 1.59/0.61  fof(f25,plain,(
% 1.59/0.61    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f13])).
% 1.59/0.61  fof(f13,axiom,(
% 1.59/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.59/0.61  fof(f71,plain,(
% 1.59/0.61    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.59/0.61    inference(definition_unfolding,[],[f35,f46])).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f42,plain,(
% 1.59/0.61    v1_xboole_0(k1_xboole_0)),
% 1.59/0.61    inference(cnf_transformation,[],[f2])).
% 1.59/0.61  fof(f2,axiom,(
% 1.59/0.61    v1_xboole_0(k1_xboole_0)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (25263)------------------------------
% 1.59/0.61  % (25263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (25263)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (25263)Memory used [KB]: 6780
% 1.59/0.61  % (25263)Time elapsed: 0.186 s
% 1.59/0.61  % (25263)------------------------------
% 1.59/0.61  % (25263)------------------------------
% 1.59/0.61  % (25234)Success in time 0.254 s
%------------------------------------------------------------------------------
