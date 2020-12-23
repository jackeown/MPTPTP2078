%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:08 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 301 expanded)
%              Number of leaves         :   20 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  302 (1046 expanded)
%              Number of equality atoms :   14 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f687,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f197,f298,f342,f573,f581,f589,f686])).

fof(f686,plain,
    ( spl3_24
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f685])).

fof(f685,plain,
    ( $false
    | spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f681,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f681,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_24
    | ~ spl3_32 ),
    inference(resolution,[],[f680,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f680,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f679,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f679,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f678,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f678,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24
    | ~ spl3_32 ),
    inference(superposition,[],[f674,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f674,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f673,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f673,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f672,f32])).

fof(f672,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f669,f567])).

fof(f567,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl3_32
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f669,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_24 ),
    inference(resolution,[],[f341,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
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
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f341,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl3_24
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f589,plain,(
    spl3_33 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | spl3_33 ),
    inference(subsumption_resolution,[],[f587,f31])).

fof(f587,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(subsumption_resolution,[],[f586,f32])).

fof(f586,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(subsumption_resolution,[],[f585,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f585,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(superposition,[],[f572,f45])).

fof(f572,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl3_33
  <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f581,plain,(
    spl3_32 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | spl3_32 ),
    inference(subsumption_resolution,[],[f579,f31])).

fof(f579,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_32 ),
    inference(subsumption_resolution,[],[f576,f32])).

fof(f576,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_32 ),
    inference(resolution,[],[f568,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f568,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f566])).

fof(f573,plain,
    ( ~ spl3_32
    | ~ spl3_33
    | spl3_23 ),
    inference(avatar_split_clause,[],[f564,f335,f570,f566])).

fof(f335,plain,
    ( spl3_23
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f564,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_23 ),
    inference(subsumption_resolution,[],[f563,f30])).

fof(f563,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_23 ),
    inference(subsumption_resolution,[],[f560,f31])).

fof(f560,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_23 ),
    inference(resolution,[],[f337,f35])).

fof(f337,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f335])).

fof(f342,plain,
    ( ~ spl3_23
    | ~ spl3_24
    | spl3_11 ),
    inference(avatar_split_clause,[],[f330,f178,f339,f335])).

fof(f178,plain,
    ( spl3_11
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f330,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_11 ),
    inference(resolution,[],[f180,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f180,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f298,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f296,f30])).

fof(f296,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f291,f49])).

fof(f49,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f291,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f220,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_10 ),
    inference(resolution,[],[f219,f80])).

fof(f80,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(X7,X5)
      | ~ r1_tarski(X7,X6)
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f42,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f75,f46])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f219,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f176,f41])).

fof(f176,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_10
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f197,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f191,f48])).

fof(f48,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f31])).

fof(f191,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f185,f102])).

fof(f102,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f99,f30])).

fof(f99,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f31])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f184,f80])).

fof(f184,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f172,f41])).

fof(f172,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f181,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f165,f178,f174,f170])).

fof(f165,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f33,f45])).

fof(f33,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (30456)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (30447)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (30451)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (30449)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (30448)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (30450)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (30469)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (30445)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.20/0.52  % (30446)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (30461)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.20/0.52  % (30466)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.20/0.53  % (30460)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.20/0.53  % (30468)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.20/0.53  % (30457)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.20/0.53  % (30452)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.33/0.53  % (30462)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.33/0.53  % (30463)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.33/0.53  % (30455)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.33/0.54  % (30470)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.33/0.54  % (30458)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.33/0.54  % (30471)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.33/0.54  % (30464)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.33/0.54  % (30467)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.33/0.54  % (30465)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.33/0.54  % (30459)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (30449)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f687,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(avatar_sat_refutation,[],[f181,f197,f298,f342,f573,f581,f589,f686])).
% 1.33/0.54  fof(f686,plain,(
% 1.33/0.54    spl3_24 | ~spl3_32),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f685])).
% 1.33/0.54  fof(f685,plain,(
% 1.33/0.54    $false | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(subsumption_resolution,[],[f681,f46])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.54    inference(equality_resolution,[],[f38])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.54    inference(flattening,[],[f27])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.54  fof(f681,plain,(
% 1.33/0.54    ~r1_tarski(sK2,sK2) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(resolution,[],[f680,f42])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.33/0.54  fof(f680,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(subsumption_resolution,[],[f679,f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.54    inference(cnf_transformation,[],[f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f25,f24,f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,negated_conjecture,(
% 1.33/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.33/0.54    inference(negated_conjecture,[],[f10])).
% 1.33/0.54  fof(f10,conjecture,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 1.33/0.54  fof(f679,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(subsumption_resolution,[],[f678,f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.54    inference(cnf_transformation,[],[f26])).
% 1.33/0.54  fof(f678,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(superposition,[],[f674,f45])).
% 1.33/0.54  fof(f45,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.54    inference(flattening,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.33/0.54  fof(f674,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(subsumption_resolution,[],[f673,f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    l1_pre_topc(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f26])).
% 1.33/0.54  fof(f673,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~l1_pre_topc(sK0) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(subsumption_resolution,[],[f672,f32])).
% 1.33/0.54  fof(f672,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_24 | ~spl3_32)),
% 1.33/0.54    inference(subsumption_resolution,[],[f669,f567])).
% 1.33/0.54  fof(f567,plain,(
% 1.33/0.54    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_32),
% 1.33/0.54    inference(avatar_component_clause,[],[f566])).
% 1.33/0.54  fof(f566,plain,(
% 1.33/0.54    spl3_32 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.33/0.54  fof(f669,plain,(
% 1.33/0.54    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_24),
% 1.33/0.54    inference(resolution,[],[f341,f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f14])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.33/0.54  fof(f341,plain,(
% 1.33/0.54    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_24),
% 1.33/0.54    inference(avatar_component_clause,[],[f339])).
% 1.33/0.54  fof(f339,plain,(
% 1.33/0.54    spl3_24 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.33/0.54  fof(f589,plain,(
% 1.33/0.54    spl3_33),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f588])).
% 1.33/0.54  fof(f588,plain,(
% 1.33/0.54    $false | spl3_33),
% 1.33/0.54    inference(subsumption_resolution,[],[f587,f31])).
% 1.33/0.54  fof(f587,plain,(
% 1.33/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 1.33/0.54    inference(subsumption_resolution,[],[f586,f32])).
% 1.33/0.54  fof(f586,plain,(
% 1.33/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 1.33/0.54    inference(subsumption_resolution,[],[f585,f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.33/0.54  fof(f585,plain,(
% 1.33/0.54    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 1.33/0.54    inference(superposition,[],[f572,f45])).
% 1.33/0.54  fof(f572,plain,(
% 1.33/0.54    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_33),
% 1.33/0.54    inference(avatar_component_clause,[],[f570])).
% 1.33/0.54  fof(f570,plain,(
% 1.33/0.54    spl3_33 <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.33/0.55  fof(f581,plain,(
% 1.33/0.55    spl3_32),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f580])).
% 1.33/0.55  fof(f580,plain,(
% 1.33/0.55    $false | spl3_32),
% 1.33/0.55    inference(subsumption_resolution,[],[f579,f31])).
% 1.33/0.55  fof(f579,plain,(
% 1.33/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_32),
% 1.33/0.55    inference(subsumption_resolution,[],[f576,f32])).
% 1.33/0.55  fof(f576,plain,(
% 1.33/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_32),
% 1.33/0.55    inference(resolution,[],[f568,f44])).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.55    inference(flattening,[],[f19])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.33/0.55    inference(ennf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.33/0.55  fof(f568,plain,(
% 1.33/0.55    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_32),
% 1.33/0.55    inference(avatar_component_clause,[],[f566])).
% 1.33/0.55  fof(f573,plain,(
% 1.33/0.55    ~spl3_32 | ~spl3_33 | spl3_23),
% 1.33/0.55    inference(avatar_split_clause,[],[f564,f335,f570,f566])).
% 1.33/0.55  fof(f335,plain,(
% 1.33/0.55    spl3_23 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.33/0.55  fof(f564,plain,(
% 1.33/0.55    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_23),
% 1.33/0.55    inference(subsumption_resolution,[],[f563,f30])).
% 1.33/0.55  fof(f563,plain,(
% 1.33/0.55    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_23),
% 1.33/0.55    inference(subsumption_resolution,[],[f560,f31])).
% 1.33/0.55  fof(f560,plain,(
% 1.33/0.55    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_23),
% 1.33/0.55    inference(resolution,[],[f337,f35])).
% 1.33/0.55  fof(f337,plain,(
% 1.33/0.55    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_23),
% 1.33/0.55    inference(avatar_component_clause,[],[f335])).
% 1.33/0.55  fof(f342,plain,(
% 1.33/0.55    ~spl3_23 | ~spl3_24 | spl3_11),
% 1.33/0.55    inference(avatar_split_clause,[],[f330,f178,f339,f335])).
% 1.33/0.55  fof(f178,plain,(
% 1.33/0.55    spl3_11 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.33/0.55  fof(f330,plain,(
% 1.33/0.55    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_11),
% 1.33/0.55    inference(resolution,[],[f180,f43])).
% 1.33/0.55  fof(f43,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.33/0.55    inference(flattening,[],[f17])).
% 1.33/0.55  fof(f17,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.33/0.55  fof(f180,plain,(
% 1.33/0.55    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_11),
% 1.33/0.55    inference(avatar_component_clause,[],[f178])).
% 1.33/0.55  fof(f298,plain,(
% 1.33/0.55    spl3_10),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f297])).
% 1.33/0.55  fof(f297,plain,(
% 1.33/0.55    $false | spl3_10),
% 1.33/0.55    inference(subsumption_resolution,[],[f296,f30])).
% 1.33/0.55  fof(f296,plain,(
% 1.33/0.55    ~l1_pre_topc(sK0) | spl3_10),
% 1.33/0.55    inference(subsumption_resolution,[],[f291,f49])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.33/0.55    inference(resolution,[],[f40,f32])).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f29])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.33/0.55    inference(nnf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.33/0.55  fof(f291,plain,(
% 1.33/0.55    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | spl3_10),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f286])).
% 1.33/0.55  fof(f286,plain,(
% 1.33/0.55    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 1.33/0.55    inference(resolution,[],[f220,f101])).
% 1.33/0.55  fof(f101,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 1.33/0.55    inference(resolution,[],[f34,f41])).
% 1.33/0.55  fof(f41,plain,(
% 1.33/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f29])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.33/0.55  fof(f220,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_10),
% 1.33/0.55    inference(resolution,[],[f219,f80])).
% 1.33/0.55  fof(f80,plain,(
% 1.33/0.55    ( ! [X6,X7,X5] : (r1_tarski(X7,X5) | ~r1_tarski(X7,X6) | ~r1_tarski(X6,X5)) )),
% 1.33/0.55    inference(superposition,[],[f42,f77])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f75,f46])).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.33/0.55    inference(resolution,[],[f52,f43])).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 1.33/0.55    inference(resolution,[],[f39,f36])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f219,plain,(
% 1.33/0.55    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_10),
% 1.33/0.55    inference(resolution,[],[f176,f41])).
% 1.33/0.55  fof(f176,plain,(
% 1.33/0.55    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 1.33/0.55    inference(avatar_component_clause,[],[f174])).
% 1.33/0.55  fof(f174,plain,(
% 1.33/0.55    spl3_10 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.33/0.55  fof(f197,plain,(
% 1.33/0.55    spl3_9),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f196])).
% 1.33/0.55  fof(f196,plain,(
% 1.33/0.55    $false | spl3_9),
% 1.33/0.55    inference(subsumption_resolution,[],[f191,f48])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.33/0.55    inference(resolution,[],[f40,f31])).
% 1.33/0.55  fof(f191,plain,(
% 1.33/0.55    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_9),
% 1.33/0.55    inference(resolution,[],[f185,f102])).
% 1.33/0.55  fof(f102,plain,(
% 1.33/0.55    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f99,f30])).
% 1.33/0.55  fof(f99,plain,(
% 1.33/0.55    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.33/0.55    inference(resolution,[],[f34,f31])).
% 1.33/0.55  fof(f185,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_9),
% 1.33/0.55    inference(resolution,[],[f184,f80])).
% 1.33/0.55  fof(f184,plain,(
% 1.33/0.55    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_9),
% 1.33/0.55    inference(resolution,[],[f172,f41])).
% 1.33/0.55  fof(f172,plain,(
% 1.33/0.55    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 1.33/0.55    inference(avatar_component_clause,[],[f170])).
% 1.33/0.55  fof(f170,plain,(
% 1.33/0.55    spl3_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.33/0.55  fof(f181,plain,(
% 1.33/0.55    ~spl3_9 | ~spl3_10 | ~spl3_11),
% 1.33/0.55    inference(avatar_split_clause,[],[f165,f178,f174,f170])).
% 1.33/0.55  fof(f165,plain,(
% 1.33/0.55    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    inference(superposition,[],[f33,f45])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (30449)------------------------------
% 1.33/0.55  % (30449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (30449)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (30449)Memory used [KB]: 6396
% 1.33/0.55  % (30449)Time elapsed: 0.137 s
% 1.33/0.55  % (30449)------------------------------
% 1.33/0.55  % (30449)------------------------------
% 1.33/0.55  % (30442)Success in time 0.184 s
%------------------------------------------------------------------------------
