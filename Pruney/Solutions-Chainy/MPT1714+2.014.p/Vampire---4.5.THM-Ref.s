%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 685 expanded)
%              Number of leaves         :   13 ( 252 expanded)
%              Depth                    :   24
%              Number of atoms          :  361 (6092 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(global_subsumption,[],[f36,f33,f148])).

fof(f148,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f147,f123])).

fof(f123,plain,(
    ! [X4] :
      ( r1_tsep_1(X4,sK3)
      | ~ m1_pre_topc(X4,sK2)
      | ~ m1_pre_topc(X4,sK0) ) ),
    inference(global_subsumption,[],[f34,f41,f59,f117])).

fof(f117,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(sK2,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_pre_topc(X4,sK2)
      | r1_tsep_1(X4,sK3)
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f114,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | r1_tsep_1(X0,sK3)
      | ~ l1_struct_0(X0) ) ),
    inference(global_subsumption,[],[f57,f110])).

fof(f110,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK3)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f108,f41])).

fof(f108,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK3)
      | r1_tsep_1(X2,sK3)
      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f106,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f106,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f56,f105])).

fof(f105,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f95,f73])).

fof(f73,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(global_subsumption,[],[f56,f72])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f70,f38])).

fof(f38,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0) )
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0) )
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0) )
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0) )
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f70,plain,(
    ! [X3] :
      ( ~ r1_tsep_1(sK3,X3)
      | ~ l1_pre_topc(X3)
      | r1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f65,f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f95,plain,(
    ! [X6,X7] :
      ( ~ r1_tsep_1(X7,sK3)
      | r1_xboole_0(X6,u1_struct_0(sK3))
      | ~ r1_tarski(X6,u1_struct_0(X7))
      | ~ l1_pre_topc(X7) ) ),
    inference(resolution,[],[f91,f57])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r1_tarski(X2,u1_struct_0(X0))
      | r1_xboole_0(X2,u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f90,f41])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ r1_tarski(X2,u1_struct_0(X0))
      | r1_xboole_0(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tarski(X2,u1_struct_0(X0))
      | r1_xboole_0(X2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f39,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f53,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_xboole_0(X0,X2)
      | sP4(X3,X0) ) ),
    inference(cnf_transformation,[],[f52_D])).

fof(f52_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r1_tarski(X2,X3)
          | r1_xboole_0(X0,X2) )
    <=> ~ sP4(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X0)
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X3) ) ),
    inference(general_splitting,[],[f49,f52_D])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f54,f34])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (5605)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f57,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(global_subsumption,[],[f32,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f56,f42])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f34,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f37,f146])).

fof(f146,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(global_subsumption,[],[f36,f33,f57,f142])).

fof(f142,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK3)
    | r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK1,X1)
      | ~ l1_pre_topc(X1)
      | r1_tsep_1(X1,sK1) ) ),
    inference(resolution,[],[f66,f55])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f54,f33])).

fof(f37,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (5620)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.48  % (5602)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (5598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (5607)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (5607)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f36,f33,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f147,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X4] : (r1_tsep_1(X4,sK3) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X4,sK0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f34,f41,f59,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,sK2) | r1_tsep_1(X4,sK3) | ~l1_struct_0(X4)) )),
% 0.21/0.49    inference(resolution,[],[f114,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | r1_tsep_1(X0,sK3) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f57,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~l1_struct_0(X0) | ~l1_pre_topc(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f108,f41])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X2] : (~l1_struct_0(sK3) | r1_tsep_1(X2,sK3) | ~r1_tarski(u1_struct_0(X2),u1_struct_0(sK2)) | ~l1_struct_0(X2)) )),
% 0.21/0.49    inference(resolution,[],[f106,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.21/0.49    inference(global_subsumption,[],[f56,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f95,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(global_subsumption,[],[f56,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~l1_pre_topc(sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~l1_pre_topc(sK2) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f70,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f25,f24,f23,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) => (? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) => ((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X3] : (~r1_tsep_1(sK3,X3) | ~l1_pre_topc(X3) | r1_tsep_1(X3,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f66,f57])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | r1_tsep_1(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f65,f41])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f45,f41])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~r1_tsep_1(X7,sK3) | r1_xboole_0(X6,u1_struct_0(sK3)) | ~r1_tarski(X6,u1_struct_0(X7)) | ~l1_pre_topc(X7)) )),
% 0.21/0.49    inference(resolution,[],[f91,f57])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~r1_tarski(X2,u1_struct_0(X0)) | r1_xboole_0(X2,u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f90,f41])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~r1_tarski(X2,u1_struct_0(X0)) | r1_xboole_0(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f77,f41])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X0) | ~r1_tarski(X2,u1_struct_0(X0)) | r1_xboole_0(X2,u1_struct_0(X1))) )),
% 0.21/0.49    inference(resolution,[],[f39,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 0.21/0.49    inference(resolution,[],[f53,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP4(X1,X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f52,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (~r1_tarski(X2,X3) | r1_xboole_0(X0,X2) | sP4(X3,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f52_D])).
% 0.21/0.49  fof(f52_D,plain,(
% 0.21/0.49    ( ! [X0,X3] : (( ! [X2] : (~r1_tarski(X2,X3) | r1_xboole_0(X0,X2)) ) <=> ~sP4(X3,X0)) )),
% 0.21/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~sP4(X3,X0) | ~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X3)) )),
% 0.21/0.49    inference(general_splitting,[],[f49,f52_D])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    l1_pre_topc(sK2)),
% 0.21/0.49    inference(resolution,[],[f54,f34])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f42,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  % (5605)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    l1_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f54,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.49    inference(global_subsumption,[],[f32,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.21/0.49    inference(resolution,[],[f44,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f56,f42])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~r1_tsep_1(sK1,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f37,f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    r1_tsep_1(sK3,sK1)),
% 0.21/0.49    inference(global_subsumption,[],[f36,f33,f57,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK3) | r1_tsep_1(sK3,sK1)),
% 0.21/0.49    inference(resolution,[],[f123,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tsep_1(sK1,X1) | ~l1_pre_topc(X1) | r1_tsep_1(X1,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f66,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f54,f33])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5607)------------------------------
% 0.21/0.49  % (5607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5607)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5607)Memory used [KB]: 6268
% 0.21/0.49  % (5607)Time elapsed: 0.081 s
% 0.21/0.49  % (5607)------------------------------
% 0.21/0.49  % (5607)------------------------------
% 0.21/0.49  % (5590)Success in time 0.133 s
%------------------------------------------------------------------------------
