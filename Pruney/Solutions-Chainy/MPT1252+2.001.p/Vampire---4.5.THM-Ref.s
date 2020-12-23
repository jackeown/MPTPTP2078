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
% DateTime   : Thu Dec  3 13:11:22 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 352 expanded)
%              Number of leaves         :   24 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          :  399 (1053 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f741,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f98,f153,f156,f279,f454,f458,f499,f611,f740])).

fof(f740,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f738,f152])).

fof(f152,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl2_4
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f738,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f737,f94])).

fof(f94,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_2
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f737,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f735,f41])).

fof(f41,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_1)).

fof(f735,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(resolution,[],[f734,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f734,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f733,f152])).

fof(f733,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f732,f94])).

fof(f732,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(superposition,[],[f48,f730])).

fof(f730,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f724,f620])).

fof(f620,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f142,f498])).

fof(f498,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl2_23
  <=> k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f142,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f136,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f136,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f43,f94])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f724,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f122,f152])).

fof(f122,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X10,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X10) )
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f94])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f611,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | spl2_22 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | spl2_22 ),
    inference(subsumption_resolution,[],[f609,f39])).

fof(f609,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_5
    | spl2_22 ),
    inference(subsumption_resolution,[],[f608,f89])).

fof(f89,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_1
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f608,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_5
    | spl2_22 ),
    inference(resolution,[],[f587,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f587,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_5
    | spl2_22 ),
    inference(subsumption_resolution,[],[f586,f494])).

fof(f494,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl2_22
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f586,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f585,f423])).

fof(f423,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f410,f39])).

fof(f410,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f585,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f584,f76])).

fof(f76,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f73,f39])).

fof(f73,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f584,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f583,f111])).

fof(f111,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f53])).

fof(f583,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f582,f39])).

fof(f582,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f566,f269])).

fof(f269,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl2_5
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f566,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f45,f423])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f499,plain,
    ( ~ spl2_22
    | spl2_23
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f474,f451,f496,f492])).

fof(f451,plain,
    ( spl2_21
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f474,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_21 ),
    inference(resolution,[],[f453,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f453,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f451])).

fof(f458,plain,
    ( ~ spl2_2
    | spl2_20 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | ~ spl2_2
    | spl2_20 ),
    inference(subsumption_resolution,[],[f456,f39])).

fof(f456,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | spl2_20 ),
    inference(subsumption_resolution,[],[f455,f94])).

fof(f455,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_20 ),
    inference(resolution,[],[f449,f52])).

fof(f449,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl2_20
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f454,plain,
    ( ~ spl2_20
    | spl2_21
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f262,f150,f92,f451,f447])).

fof(f262,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f249,f94])).

fof(f249,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f50,f200])).

fof(f200,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f199,f94])).

fof(f199,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f188,f152])).

fof(f188,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f48,f142])).

fof(f279,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f277,f39])).

fof(f277,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(subsumption_resolution,[],[f276,f40])).

fof(f276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(resolution,[],[f270,f52])).

fof(f270,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f268])).

fof(f156,plain,
    ( ~ spl2_2
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl2_2
    | spl2_3 ),
    inference(subsumption_resolution,[],[f154,f94])).

fof(f154,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(resolution,[],[f148,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f148,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_3
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f153,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f116,f92,f150,f146])).

fof(f116,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f115,f39])).

fof(f115,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f51,f103])).

fof(f103,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f99,f39])).

fof(f99,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f98,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1 ),
    inference(resolution,[],[f90,f46])).

fof(f90,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f86,f92,f88])).

fof(f86,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f51,f84])).

fof(f84,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f81,f39])).

fof(f81,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (30478)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (30467)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (30486)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (30476)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (30468)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (30480)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (30470)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (30473)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (30487)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (30472)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (30471)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (30469)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (30479)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (30475)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (30492)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (30474)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (30489)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (30488)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (30491)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (30490)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (30481)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (30484)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (30485)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (30477)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.57  % (30483)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.57  % (30482)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.58  % (30476)Refutation not found, incomplete strategy% (30476)------------------------------
% 0.21/0.58  % (30476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (30476)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (30476)Memory used [KB]: 6012
% 1.69/0.59  % (30476)Time elapsed: 0.158 s
% 1.69/0.59  % (30476)------------------------------
% 1.69/0.59  % (30476)------------------------------
% 1.83/0.61  % (30492)Refutation found. Thanks to Tanya!
% 1.83/0.61  % SZS status Theorem for theBenchmark
% 1.83/0.61  % SZS output start Proof for theBenchmark
% 1.83/0.61  fof(f741,plain,(
% 1.83/0.61    $false),
% 1.83/0.61    inference(avatar_sat_refutation,[],[f95,f98,f153,f156,f279,f454,f458,f499,f611,f740])).
% 1.83/0.61  fof(f740,plain,(
% 1.83/0.61    ~spl2_2 | ~spl2_4 | ~spl2_23),
% 1.83/0.61    inference(avatar_contradiction_clause,[],[f739])).
% 1.83/0.61  fof(f739,plain,(
% 1.83/0.61    $false | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(subsumption_resolution,[],[f738,f152])).
% 1.83/0.61  fof(f152,plain,(
% 1.83/0.61    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 1.83/0.61    inference(avatar_component_clause,[],[f150])).
% 1.83/0.61  fof(f150,plain,(
% 1.83/0.61    spl2_4 <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.83/0.61  fof(f738,plain,(
% 1.83/0.61    ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(subsumption_resolution,[],[f737,f94])).
% 1.83/0.61  fof(f94,plain,(
% 1.83/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.83/0.61    inference(avatar_component_clause,[],[f92])).
% 1.83/0.61  fof(f92,plain,(
% 1.83/0.61    spl2_2 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.83/0.61  fof(f737,plain,(
% 1.83/0.61    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(subsumption_resolution,[],[f735,f41])).
% 1.83/0.61  fof(f41,plain,(
% 1.83/0.61    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 1.83/0.61    inference(cnf_transformation,[],[f35])).
% 1.83/0.61  fof(f35,plain,(
% 1.83/0.61    (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.83/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f34,f33])).
% 1.83/0.61  fof(f33,plain,(
% 1.83/0.61    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.83/0.61    introduced(choice_axiom,[])).
% 1.83/0.61  fof(f34,plain,(
% 1.83/0.61    ? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.83/0.61    introduced(choice_axiom,[])).
% 1.83/0.61  fof(f16,plain,(
% 1.83/0.61    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.83/0.61    inference(ennf_transformation,[],[f15])).
% 1.83/0.61  fof(f15,negated_conjecture,(
% 1.83/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 1.83/0.61    inference(negated_conjecture,[],[f14])).
% 1.83/0.61  fof(f14,conjecture,(
% 1.83/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_1)).
% 1.83/0.61  fof(f735,plain,(
% 1.83/0.61    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(resolution,[],[f734,f50])).
% 1.83/0.61  fof(f50,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f36])).
% 1.83/0.61  fof(f36,plain,(
% 1.83/0.61    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.61    inference(nnf_transformation,[],[f24])).
% 1.83/0.61  fof(f24,plain,(
% 1.83/0.61    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f5])).
% 1.83/0.61  fof(f5,axiom,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.83/0.61  fof(f734,plain,(
% 1.83/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(subsumption_resolution,[],[f733,f152])).
% 1.83/0.61  fof(f733,plain,(
% 1.83/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(subsumption_resolution,[],[f732,f94])).
% 1.83/0.61  fof(f732,plain,(
% 1.83/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(superposition,[],[f48,f730])).
% 1.83/0.61  fof(f730,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 1.83/0.61    inference(forward_demodulation,[],[f724,f620])).
% 1.83/0.61  fof(f620,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_23)),
% 1.83/0.61    inference(backward_demodulation,[],[f142,f498])).
% 1.83/0.61  fof(f498,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 1.83/0.61    inference(avatar_component_clause,[],[f496])).
% 1.83/0.61  fof(f496,plain,(
% 1.83/0.61    spl2_23 <=> k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.83/0.61  fof(f142,plain,(
% 1.83/0.61    k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 1.83/0.61    inference(subsumption_resolution,[],[f136,f39])).
% 1.83/0.61  fof(f39,plain,(
% 1.83/0.61    l1_pre_topc(sK0)),
% 1.83/0.61    inference(cnf_transformation,[],[f35])).
% 1.83/0.61  fof(f136,plain,(
% 1.83/0.61    k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.83/0.61    inference(resolution,[],[f43,f94])).
% 1.83/0.61  fof(f43,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f18])).
% 1.83/0.61  fof(f18,plain,(
% 1.83/0.61    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(ennf_transformation,[],[f13])).
% 1.83/0.61  fof(f13,axiom,(
% 1.83/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.83/0.61  fof(f724,plain,(
% 1.83/0.61    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_4)),
% 1.83/0.61    inference(resolution,[],[f122,f152])).
% 1.83/0.61  fof(f122,plain,(
% 1.83/0.61    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X10,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X10)) ) | ~spl2_2),
% 1.83/0.61    inference(resolution,[],[f57,f94])).
% 1.83/0.61  fof(f57,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f32])).
% 1.83/0.61  fof(f32,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.61    inference(flattening,[],[f31])).
% 1.83/0.61  fof(f31,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.83/0.61    inference(ennf_transformation,[],[f2])).
% 1.83/0.61  fof(f2,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.83/0.61  fof(f48,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f23])).
% 1.83/0.61  fof(f23,plain,(
% 1.83/0.61    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f6])).
% 1.83/0.61  fof(f6,axiom,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 1.83/0.61  fof(f611,plain,(
% 1.83/0.61    ~spl2_1 | ~spl2_5 | spl2_22),
% 1.83/0.61    inference(avatar_contradiction_clause,[],[f610])).
% 1.83/0.61  fof(f610,plain,(
% 1.83/0.61    $false | (~spl2_1 | ~spl2_5 | spl2_22)),
% 1.83/0.61    inference(subsumption_resolution,[],[f609,f39])).
% 1.83/0.61  fof(f609,plain,(
% 1.83/0.61    ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_5 | spl2_22)),
% 1.83/0.61    inference(subsumption_resolution,[],[f608,f89])).
% 1.83/0.61  fof(f89,plain,(
% 1.83/0.61    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_1),
% 1.83/0.61    inference(avatar_component_clause,[],[f88])).
% 1.83/0.61  fof(f88,plain,(
% 1.83/0.61    spl2_1 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.83/0.61  fof(f608,plain,(
% 1.83/0.61    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_5 | spl2_22)),
% 1.83/0.61    inference(resolution,[],[f587,f52])).
% 1.83/0.61  fof(f52,plain,(
% 1.83/0.61    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f28])).
% 1.83/0.61  fof(f28,plain,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(flattening,[],[f27])).
% 1.83/0.61  fof(f27,plain,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f7])).
% 1.83/0.61  fof(f7,axiom,(
% 1.83/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.83/0.61  fof(f587,plain,(
% 1.83/0.61    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_5 | spl2_22)),
% 1.83/0.61    inference(subsumption_resolution,[],[f586,f494])).
% 1.83/0.61  fof(f494,plain,(
% 1.83/0.61    ~r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | spl2_22),
% 1.83/0.61    inference(avatar_component_clause,[],[f492])).
% 1.83/0.61  fof(f492,plain,(
% 1.83/0.61    spl2_22 <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.83/0.61  fof(f586,plain,(
% 1.83/0.61    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_5)),
% 1.83/0.61    inference(forward_demodulation,[],[f585,f423])).
% 1.83/0.61  fof(f423,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.83/0.61    inference(subsumption_resolution,[],[f410,f39])).
% 1.83/0.61  fof(f410,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 1.83/0.61    inference(resolution,[],[f44,f40])).
% 1.83/0.61  fof(f40,plain,(
% 1.83/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    inference(cnf_transformation,[],[f35])).
% 1.83/0.61  fof(f44,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f19])).
% 1.83/0.61  fof(f19,plain,(
% 1.83/0.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(ennf_transformation,[],[f10])).
% 1.83/0.61  fof(f10,axiom,(
% 1.83/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 1.83/0.61  fof(f585,plain,(
% 1.83/0.61    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_5)),
% 1.83/0.61    inference(forward_demodulation,[],[f584,f76])).
% 1.83/0.61  fof(f76,plain,(
% 1.83/0.61    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),
% 1.83/0.61    inference(subsumption_resolution,[],[f73,f39])).
% 1.83/0.61  fof(f73,plain,(
% 1.83/0.61    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.83/0.61    inference(resolution,[],[f53,f40])).
% 1.83/0.61  fof(f53,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f30])).
% 1.83/0.61  fof(f30,plain,(
% 1.83/0.61    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(flattening,[],[f29])).
% 1.83/0.61  fof(f29,plain,(
% 1.83/0.61    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f8])).
% 1.83/0.61  fof(f8,axiom,(
% 1.83/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 1.83/0.61  fof(f584,plain,(
% 1.83/0.61    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_5)),
% 1.83/0.61    inference(forward_demodulation,[],[f583,f111])).
% 1.83/0.61  fof(f111,plain,(
% 1.83/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_1),
% 1.83/0.61    inference(subsumption_resolution,[],[f106,f39])).
% 1.83/0.61  fof(f106,plain,(
% 1.83/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 1.83/0.61    inference(resolution,[],[f89,f53])).
% 1.83/0.61  fof(f583,plain,(
% 1.83/0.61    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 1.83/0.61    inference(subsumption_resolution,[],[f582,f39])).
% 1.83/0.61  fof(f582,plain,(
% 1.83/0.61    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_5),
% 1.83/0.61    inference(subsumption_resolution,[],[f566,f269])).
% 1.83/0.61  fof(f269,plain,(
% 1.83/0.61    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 1.83/0.61    inference(avatar_component_clause,[],[f268])).
% 1.83/0.61  fof(f268,plain,(
% 1.83/0.61    spl2_5 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.83/0.61  fof(f566,plain,(
% 1.83/0.61    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.83/0.61    inference(superposition,[],[f45,f423])).
% 1.83/0.61  fof(f45,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f20])).
% 1.83/0.61  fof(f20,plain,(
% 1.83/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(ennf_transformation,[],[f9])).
% 1.83/0.61  fof(f9,axiom,(
% 1.83/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 1.83/0.61  fof(f499,plain,(
% 1.83/0.61    ~spl2_22 | spl2_23 | ~spl2_21),
% 1.83/0.61    inference(avatar_split_clause,[],[f474,f451,f496,f492])).
% 1.83/0.61  fof(f451,plain,(
% 1.83/0.61    spl2_21 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.83/0.61  fof(f474,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl2_21),
% 1.83/0.61    inference(resolution,[],[f453,f56])).
% 1.83/0.61  fof(f56,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f38])).
% 1.83/0.61  fof(f38,plain,(
% 1.83/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.61    inference(flattening,[],[f37])).
% 1.83/0.61  fof(f37,plain,(
% 1.83/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.61    inference(nnf_transformation,[],[f1])).
% 1.83/0.61  fof(f1,axiom,(
% 1.83/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.61  fof(f453,plain,(
% 1.83/0.61    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) | ~spl2_21),
% 1.83/0.61    inference(avatar_component_clause,[],[f451])).
% 1.83/0.61  fof(f458,plain,(
% 1.83/0.61    ~spl2_2 | spl2_20),
% 1.83/0.61    inference(avatar_contradiction_clause,[],[f457])).
% 1.83/0.61  fof(f457,plain,(
% 1.83/0.61    $false | (~spl2_2 | spl2_20)),
% 1.83/0.61    inference(subsumption_resolution,[],[f456,f39])).
% 1.83/0.61  fof(f456,plain,(
% 1.83/0.61    ~l1_pre_topc(sK0) | (~spl2_2 | spl2_20)),
% 1.83/0.61    inference(subsumption_resolution,[],[f455,f94])).
% 1.83/0.61  fof(f455,plain,(
% 1.83/0.61    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_20),
% 1.83/0.61    inference(resolution,[],[f449,f52])).
% 1.83/0.61  fof(f449,plain,(
% 1.83/0.61    ~m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_20),
% 1.83/0.61    inference(avatar_component_clause,[],[f447])).
% 1.83/0.61  fof(f447,plain,(
% 1.83/0.61    spl2_20 <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.83/0.61  fof(f454,plain,(
% 1.83/0.61    ~spl2_20 | spl2_21 | ~spl2_2 | ~spl2_4),
% 1.83/0.61    inference(avatar_split_clause,[],[f262,f150,f92,f451,f447])).
% 1.83/0.61  fof(f262,plain,(
% 1.83/0.61    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4)),
% 1.83/0.61    inference(subsumption_resolution,[],[f249,f94])).
% 1.83/0.61  fof(f249,plain,(
% 1.83/0.61    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4)),
% 1.83/0.61    inference(resolution,[],[f50,f200])).
% 1.83/0.61  fof(f200,plain,(
% 1.83/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_4)),
% 1.83/0.61    inference(subsumption_resolution,[],[f199,f94])).
% 1.83/0.61  fof(f199,plain,(
% 1.83/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4)),
% 1.83/0.61    inference(subsumption_resolution,[],[f188,f152])).
% 1.83/0.61  fof(f188,plain,(
% 1.83/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.83/0.61    inference(superposition,[],[f48,f142])).
% 1.83/0.61  fof(f279,plain,(
% 1.83/0.61    spl2_5),
% 1.83/0.61    inference(avatar_contradiction_clause,[],[f278])).
% 1.83/0.61  fof(f278,plain,(
% 1.83/0.61    $false | spl2_5),
% 1.83/0.61    inference(subsumption_resolution,[],[f277,f39])).
% 1.83/0.61  fof(f277,plain,(
% 1.83/0.61    ~l1_pre_topc(sK0) | spl2_5),
% 1.83/0.61    inference(subsumption_resolution,[],[f276,f40])).
% 1.83/0.61  fof(f276,plain,(
% 1.83/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_5),
% 1.83/0.61    inference(resolution,[],[f270,f52])).
% 1.83/0.61  fof(f270,plain,(
% 1.83/0.61    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_5),
% 1.83/0.61    inference(avatar_component_clause,[],[f268])).
% 1.83/0.61  fof(f156,plain,(
% 1.83/0.61    ~spl2_2 | spl2_3),
% 1.83/0.61    inference(avatar_contradiction_clause,[],[f155])).
% 1.83/0.61  fof(f155,plain,(
% 1.83/0.61    $false | (~spl2_2 | spl2_3)),
% 1.83/0.61    inference(subsumption_resolution,[],[f154,f94])).
% 1.83/0.61  fof(f154,plain,(
% 1.83/0.61    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 1.83/0.61    inference(resolution,[],[f148,f46])).
% 1.83/0.61  fof(f46,plain,(
% 1.83/0.61    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f21])).
% 1.83/0.61  fof(f21,plain,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f3])).
% 1.83/0.61  fof(f3,axiom,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.83/0.61  fof(f148,plain,(
% 1.83/0.61    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 1.83/0.61    inference(avatar_component_clause,[],[f146])).
% 1.83/0.61  fof(f146,plain,(
% 1.83/0.61    spl2_3 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.83/0.61  fof(f153,plain,(
% 1.83/0.61    ~spl2_3 | spl2_4 | ~spl2_2),
% 1.83/0.61    inference(avatar_split_clause,[],[f116,f92,f150,f146])).
% 1.83/0.61  fof(f116,plain,(
% 1.83/0.61    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.83/0.61    inference(subsumption_resolution,[],[f115,f39])).
% 1.83/0.61  fof(f115,plain,(
% 1.83/0.61    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.83/0.61    inference(superposition,[],[f51,f103])).
% 1.83/0.61  fof(f103,plain,(
% 1.83/0.61    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_2),
% 1.83/0.61    inference(subsumption_resolution,[],[f99,f39])).
% 1.83/0.61  fof(f99,plain,(
% 1.83/0.61    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.83/0.61    inference(resolution,[],[f94,f42])).
% 1.83/0.61  fof(f42,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f17])).
% 1.83/0.61  fof(f17,plain,(
% 1.83/0.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(ennf_transformation,[],[f12])).
% 1.83/0.61  fof(f12,axiom,(
% 1.83/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 1.83/0.61  fof(f51,plain,(
% 1.83/0.61    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f26])).
% 1.83/0.61  fof(f26,plain,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.83/0.61    inference(flattening,[],[f25])).
% 1.83/0.61  fof(f25,plain,(
% 1.83/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f11])).
% 1.83/0.61  fof(f11,axiom,(
% 1.83/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.83/0.61  fof(f98,plain,(
% 1.83/0.61    spl2_1),
% 1.83/0.61    inference(avatar_contradiction_clause,[],[f97])).
% 1.83/0.61  fof(f97,plain,(
% 1.83/0.61    $false | spl2_1),
% 1.83/0.61    inference(subsumption_resolution,[],[f96,f40])).
% 1.83/0.61  fof(f96,plain,(
% 1.83/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_1),
% 1.83/0.61    inference(resolution,[],[f90,f46])).
% 1.83/0.61  fof(f90,plain,(
% 1.83/0.61    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_1),
% 1.83/0.61    inference(avatar_component_clause,[],[f88])).
% 1.83/0.61  fof(f95,plain,(
% 1.83/0.61    ~spl2_1 | spl2_2),
% 1.83/0.61    inference(avatar_split_clause,[],[f86,f92,f88])).
% 1.83/0.61  fof(f86,plain,(
% 1.83/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.83/0.61    inference(subsumption_resolution,[],[f85,f39])).
% 1.83/0.61  fof(f85,plain,(
% 1.83/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.83/0.61    inference(superposition,[],[f51,f84])).
% 1.83/0.61  fof(f84,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.83/0.61    inference(subsumption_resolution,[],[f81,f39])).
% 1.83/0.61  fof(f81,plain,(
% 1.83/0.61    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 1.83/0.61    inference(resolution,[],[f42,f40])).
% 1.83/0.61  % SZS output end Proof for theBenchmark
% 1.83/0.61  % (30492)------------------------------
% 1.83/0.61  % (30492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (30492)Termination reason: Refutation
% 1.83/0.61  
% 1.83/0.61  % (30492)Memory used [KB]: 11257
% 1.83/0.61  % (30492)Time elapsed: 0.185 s
% 1.83/0.61  % (30492)------------------------------
% 1.83/0.61  % (30492)------------------------------
% 1.83/0.62  % (30466)Success in time 0.245 s
%------------------------------------------------------------------------------
