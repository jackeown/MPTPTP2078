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
% DateTime   : Thu Dec  3 13:13:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 (1342 expanded)
%              Number of leaves         :   17 ( 406 expanded)
%              Depth                    :   26
%              Number of atoms          :  381 (6294 expanded)
%              Number of equality atoms :   28 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f195,f238,f774,f834])).

fof(f834,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f832,f131])).

fof(f131,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f123,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
      | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) )
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(sK0,X1),sK0)
            | ~ v4_tops_1(k1_tops_1(sK0,X1),sK0) )
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ~ v4_tops_1(k2_pre_topc(sK0,X1),sK0)
          | ~ v4_tops_1(k1_tops_1(sK0,X1),sK0) )
        & v4_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
        | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) )
      & v4_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
                & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
              & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).

fof(f123,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f90,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f89,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f832,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f831,f94])).

fof(f94,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f93,f40])).

fof(f93,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f831,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f830,f40])).

fof(f830,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f829,f90])).

fof(f829,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f828,f65])).

fof(f65,plain,
    ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_1
  <=> v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f828,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f820,f341])).

fof(f341,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f340,f151])).

fof(f151,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f143,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f92,f52])).

fof(f92,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f91,f40])).

fof(f91,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f340,plain,(
    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f339,f40])).

fof(f339,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f338,f41])).

fof(f338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f156,f148])).

fof(f148,plain,(
    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f92,f50])).

fof(f156,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(X1,sK1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f99,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f99,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f98,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f42,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f820,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f47,f790])).

fof(f790,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f789,f345])).

fof(f345,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f344,f137])).

fof(f137,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f129,f40])).

fof(f129,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f90,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f344,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f343,f40])).

fof(f343,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f342,f41])).

fof(f342,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f169,f134])).

fof(f134,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f127,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f90,f51])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,sK1),k2_pre_topc(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f102,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f101,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tops_1(X1,X0)
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f789,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f788,f507])).

fof(f507,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f505,f341])).

fof(f505,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f332,f56])).

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

fof(f332,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f331,f40])).

fof(f331,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f330,f41])).

fof(f330,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f110,f92])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,sK1),k1_tops_1(X1,k2_pre_topc(sK0,sK1)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f88,f48])).

fof(f88,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f41])).

fof(f788,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f619,f507])).

fof(f619,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f337,f56])).

fof(f337,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f336,f40])).

fof(f336,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f335,f41])).

fof(f335,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f155,f148])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(X0,sK1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f99,f49])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f774,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f773])).

fof(f773,plain,
    ( $false
    | spl2_11 ),
    inference(subsumption_resolution,[],[f756,f345])).

fof(f756,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | spl2_11 ),
    inference(superposition,[],[f190,f507])).

fof(f190,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl2_11
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f238,plain,(
    spl2_12 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl2_12 ),
    inference(subsumption_resolution,[],[f236,f194])).

fof(f194,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_12
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f236,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f111,f99])).

fof(f111,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r1_tarski(X2,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f195,plain,
    ( ~ spl2_11
    | ~ spl2_12
    | spl2_2 ),
    inference(avatar_split_clause,[],[f186,f67,f192,f188])).

fof(f67,plain,
    ( spl2_2
  <=> v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f186,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f185,f40])).

fof(f185,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f184,f92])).

fof(f184,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f183,f69])).

fof(f69,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f183,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f47,f96])).

fof(f96,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f41])).

fof(f70,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f67,f63])).

fof(f43,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (26789)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (26781)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (26782)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (26802)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (26788)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (26793)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (26780)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (26779)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (26799)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (26784)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (26785)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (26783)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (26778)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (26803)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (26794)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (26798)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (26800)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (26805)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (26786)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (26791)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (26790)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (26796)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (26788)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f835,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f70,f195,f238,f774,f834])).
% 0.21/0.53  fof(f834,plain,(
% 0.21/0.53    spl2_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f833])).
% 0.21/0.53  fof(f833,plain,(
% 0.21/0.53    $false | spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f832,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ((~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f33,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v4_tops_1(k2_pre_topc(sK0,X1),sK0) | ~v4_tops_1(k1_tops_1(sK0,X1),sK0)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X1] : ((~v4_tops_1(k2_pre_topc(sK0,X1),sK0) | ~v4_tops_1(k1_tops_1(sK0,X1),sK0)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f90,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f89,f40])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f50,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.53  fof(f832,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | spl2_1),
% 0.21/0.53    inference(forward_demodulation,[],[f831,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f40])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f52,f41])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.21/0.53  fof(f831,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f830,f40])).
% 0.21/0.53  fof(f830,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f829,f90])).
% 0.21/0.53  fof(f829,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f828,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~v4_tops_1(k1_tops_1(sK0,sK1),sK0) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl2_1 <=> v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f828,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | v4_tops_1(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f820,f341])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f340,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f40])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f92,f52])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f40])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f51,f41])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f339,f40])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f338,f41])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f156,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f40])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f92,f50])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(X1,sK1)) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f99,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f40])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f97,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v4_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~v4_tops_1(sK1,sK0) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f45,f41])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 0.21/0.53  fof(f820,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | v4_tops_1(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(superposition,[],[f47,f790])).
% 0.21/0.53  fof(f790,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f789,f345])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f344,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f40])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f90,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f343,f40])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f342,f41])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f169,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f40])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f90,f51])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,sK1),k2_pre_topc(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f102,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f101,f40])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f42])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~v4_tops_1(sK1,sK0) | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f46,f41])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tops_1(X1,X0) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f789,plain,(
% 0.21/0.53    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f788,f507])).
% 0.21/0.53  fof(f507,plain,(
% 0.21/0.53    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f505,f341])).
% 0.21/0.53  fof(f505,plain,(
% 0.21/0.53    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f332,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f331,f40])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f330,f41])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f110,f92])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,sK1),k1_tops_1(X1,k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f88,f48])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f40])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f44,f41])).
% 0.21/0.53  fof(f788,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))),
% 0.21/0.53    inference(forward_demodulation,[],[f619,f507])).
% 0.21/0.53  fof(f619,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))),
% 0.21/0.53    inference(resolution,[],[f337,f56])).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f336,f40])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f335,f41])).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f155,f148])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(X0,sK1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f99,f49])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f774,plain,(
% 0.21/0.53    spl2_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f773])).
% 0.21/0.53  fof(f773,plain,(
% 0.21/0.53    $false | spl2_11),
% 0.21/0.53    inference(subsumption_resolution,[],[f756,f345])).
% 0.21/0.53  fof(f756,plain,(
% 0.21/0.53    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | spl2_11),
% 0.21/0.53    inference(superposition,[],[f190,f507])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | spl2_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    spl2_11 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    spl2_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    $false | spl2_12),
% 0.21/0.53    inference(subsumption_resolution,[],[f236,f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | spl2_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f192])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    spl2_12 <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f111,f99])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(X2,sK1) | r1_tarski(X2,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.53    inference(resolution,[],[f88,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ~spl2_11 | ~spl2_12 | spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f186,f67,f192,f188])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl2_2 <=> v4_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f185,f40])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | ~l1_pre_topc(sK0) | spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f92])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(superposition,[],[f47,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f40])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f53,f41])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f67,f63])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26788)------------------------------
% 0.21/0.53  % (26788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26788)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26788)Memory used [KB]: 11001
% 0.21/0.53  % (26788)Time elapsed: 0.118 s
% 0.21/0.53  % (26788)------------------------------
% 0.21/0.53  % (26788)------------------------------
% 0.21/0.53  % (26792)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (26775)Success in time 0.175 s
%------------------------------------------------------------------------------
