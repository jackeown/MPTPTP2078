%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1861+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 217 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 (1099 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11699,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11698,f11603])).

fof(f11603,plain,(
    v2_tex_2(sK11,sK10) ),
    inference(resolution,[],[f9505,f7175])).

fof(f7175,plain,(
    ~ v2_tex_2(k3_xboole_0(sK11,sK12),sK10) ),
    inference(backward_demodulation,[],[f4102,f4930])).

fof(f4930,plain,(
    ! [X107] : k3_xboole_0(X107,sK12) = k9_subset_1(u1_struct_0(sK10),X107,sK12) ),
    inference(resolution,[],[f4100,f4166])).

fof(f4166,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3690])).

fof(f3690,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f4100,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(cnf_transformation,[],[f3925])).

fof(f3925,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),sK11,sK12),sK10)
    & ( v2_tex_2(sK12,sK10)
      | v2_tex_2(sK11,sK10) )
    & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK10)))
    & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
    & l1_pre_topc(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f3678,f3924,f3923,f3922])).

fof(f3922,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),X1,X2),sK10)
              & ( v2_tex_2(X2,sK10)
                | v2_tex_2(X1,sK10) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK10))) )
      & l1_pre_topc(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f3923,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),X1,X2),sK10)
            & ( v2_tex_2(X2,sK10)
              | v2_tex_2(X1,sK10) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK10))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),sK11,X2),sK10)
          & ( v2_tex_2(X2,sK10)
            | v2_tex_2(sK11,sK10) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10))) )
      & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10))) ) ),
    introduced(choice_axiom,[])).

fof(f3924,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),sK11,X2),sK10)
        & ( v2_tex_2(X2,sK10)
          | v2_tex_2(sK11,sK10) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),sK11,sK12),sK10)
      & ( v2_tex_2(sK12,sK10)
        | v2_tex_2(sK11,sK10) )
      & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK10))) ) ),
    introduced(choice_axiom,[])).

fof(f3678,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3677])).

fof(f3677,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3663])).

fof(f3663,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3662])).

fof(f3662,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f4102,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK10),sK11,sK12),sK10) ),
    inference(cnf_transformation,[],[f3925])).

fof(f9505,plain,(
    ! [X6] :
      ( v2_tex_2(k3_xboole_0(X6,sK12),sK10)
      | v2_tex_2(sK11,sK10) ) ),
    inference(subsumption_resolution,[],[f9468,f5684])).

fof(f5684,plain,(
    ! [X7] : r1_tarski(k3_xboole_0(X7,sK12),sK12) ),
    inference(forward_demodulation,[],[f5683,f5577])).

fof(f5577,plain,(
    sK12 = k2_xboole_0(sK12,sK12) ),
    inference(superposition,[],[f4405,f5015])).

fof(f5015,plain,(
    sK12 = k3_xboole_0(sK12,u1_struct_0(sK10)) ),
    inference(resolution,[],[f4959,f4402])).

fof(f4402,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3853])).

fof(f3853,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4959,plain,(
    r1_tarski(sK12,u1_struct_0(sK10)) ),
    inference(resolution,[],[f4100,f4350])).

fof(f4350,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4062])).

fof(f4062,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f4405,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f5683,plain,(
    ! [X7] : r1_tarski(k3_xboole_0(X7,k2_xboole_0(sK12,sK12)),sK12) ),
    inference(forward_demodulation,[],[f5668,f4391])).

fof(f4391,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f5668,plain,(
    ! [X7] : r1_tarski(k2_xboole_0(k3_xboole_0(X7,sK12),k3_xboole_0(X7,sK12)),sK12) ),
    inference(superposition,[],[f4393,f5577])).

fof(f4393,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f9468,plain,(
    ! [X6] :
      ( v2_tex_2(k3_xboole_0(X6,sK12),sK10)
      | ~ r1_tarski(k3_xboole_0(X6,sK12),sK12)
      | v2_tex_2(sK11,sK10) ) ),
    inference(resolution,[],[f5047,f7205])).

fof(f7205,plain,(
    ! [X31] : m1_subset_1(k3_xboole_0(X31,sK12),k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(subsumption_resolution,[],[f7199,f4100])).

fof(f7199,plain,(
    ! [X31] :
      ( m1_subset_1(k3_xboole_0(X31,sK12),k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK10))) ) ),
    inference(superposition,[],[f4167,f4930])).

fof(f4167,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3691])).

fof(f3691,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f5047,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK10)))
      | v2_tex_2(X4,sK10)
      | ~ r1_tarski(X4,sK12)
      | v2_tex_2(sK11,sK10) ) ),
    inference(subsumption_resolution,[],[f5046,f4098])).

fof(f4098,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f3925])).

fof(f5046,plain,(
    ! [X4] :
      ( v2_tex_2(sK11,sK10)
      | v2_tex_2(X4,sK10)
      | ~ r1_tarski(X4,sK12)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ l1_pre_topc(sK10) ) ),
    inference(subsumption_resolution,[],[f5037,f4100])).

fof(f5037,plain,(
    ! [X4] :
      ( v2_tex_2(sK11,sK10)
      | v2_tex_2(X4,sK10)
      | ~ r1_tarski(X4,sK12)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ l1_pre_topc(sK10) ) ),
    inference(resolution,[],[f4101,f4178])).

fof(f4178,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3702])).

fof(f3702,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3701])).

fof(f3701,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3661])).

fof(f3661,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f4101,plain,
    ( v2_tex_2(sK12,sK10)
    | v2_tex_2(sK11,sK10) ),
    inference(cnf_transformation,[],[f3925])).

fof(f11698,plain,(
    ~ v2_tex_2(sK11,sK10) ),
    inference(subsumption_resolution,[],[f11669,f4408])).

fof(f4408,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f11669,plain,
    ( ~ r1_tarski(k3_xboole_0(sK11,sK12),sK11)
    | ~ v2_tex_2(sK11,sK10) ),
    inference(resolution,[],[f11480,f4099])).

fof(f4099,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(cnf_transformation,[],[f3925])).

fof(f11480,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ r1_tarski(k3_xboole_0(sK11,sK12),X2)
      | ~ v2_tex_2(X2,sK10) ) ),
    inference(subsumption_resolution,[],[f7223,f7734])).

fof(f7734,plain,(
    ! [X15] : m1_subset_1(k3_xboole_0(sK11,X15),k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(superposition,[],[f6863,f4407])).

fof(f4407,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6863,plain,(
    ! [X31] : m1_subset_1(k3_xboole_0(X31,sK11),k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(subsumption_resolution,[],[f6857,f4099])).

fof(f6857,plain,(
    ! [X31] :
      ( m1_subset_1(k3_xboole_0(X31,sK11),k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10))) ) ),
    inference(superposition,[],[f4167,f4735])).

fof(f4735,plain,(
    ! [X107] : k3_xboole_0(X107,sK11) = k9_subset_1(u1_struct_0(sK10),X107,sK11) ),
    inference(resolution,[],[f4099,f4166])).

fof(f7223,plain,(
    ! [X2] :
      ( ~ v2_tex_2(X2,sK10)
      | ~ r1_tarski(k3_xboole_0(sK11,sK12),X2)
      | ~ m1_subset_1(k3_xboole_0(sK11,sK12),k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10))) ) ),
    inference(subsumption_resolution,[],[f7210,f4098])).

fof(f7210,plain,(
    ! [X2] :
      ( ~ v2_tex_2(X2,sK10)
      | ~ r1_tarski(k3_xboole_0(sK11,sK12),X2)
      | ~ m1_subset_1(k3_xboole_0(sK11,sK12),k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ l1_pre_topc(sK10) ) ),
    inference(resolution,[],[f7175,f4178])).
%------------------------------------------------------------------------------
