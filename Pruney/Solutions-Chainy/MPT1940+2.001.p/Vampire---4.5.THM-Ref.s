%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 (1683 expanded)
%              Number of leaves         :   17 ( 622 expanded)
%              Depth                    :   20
%              Number of atoms          :  380 (12827 expanded)
%              Number of equality atoms :   42 (1668 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(global_subsumption,[],[f134,f149,f143])).

% (18338)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f143,plain,
    ( r2_hidden(sK3,sK4)
    | ~ sP0(sK2,sK3,sK4) ),
    inference(superposition,[],[f66,f136])).

fof(f136,plain,(
    sK4 = sK5(sK2,sK3,sK4) ),
    inference(resolution,[],[f134,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ v3_pre_topc(X3,X0)
            | ~ r2_hidden(X1,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ( v3_pre_topc(sK5(X0,X1,X2),X0)
          & r2_hidden(X1,sK5(X0,X1,X2))
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_pre_topc(X4,X0)
          & r2_hidden(X1,X4)
          & X2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK5(X0,X1,X2),X0)
        & r2_hidden(X1,sK5(X0,X1,X2))
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ v3_pre_topc(X3,X0)
            | ~ r2_hidden(X1,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X4] :
            ( v3_pre_topc(X4,X0)
            & r2_hidden(X1,X4)
            & X2 = X4
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ v3_pre_topc(X3,X1)
            | ~ r2_hidden(X2,X3)
            | X0 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( v3_pre_topc(X3,X1)
          & r2_hidden(X2,X3)
          & X0 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK5(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f149,plain,(
    ~ r2_hidden(sK3,sK4) ),
    inference(subsumption_resolution,[],[f147,f148])).

fof(f148,plain,(
    v3_pre_topc(sK4,sK2) ),
    inference(global_subsumption,[],[f134,f142])).

fof(f142,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ sP0(sK2,sK3,sK4) ),
    inference(superposition,[],[f67,f136])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f147,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ v3_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f70,f146])).

fof(f146,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f134,f141])).

fof(f141,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK2,sK3,sK4) ),
    inference(superposition,[],[f64,f136])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,sK4)
    | ~ v3_pre_topc(sK4,sK2) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK2)
      | ~ r2_hidden(sK3,X3)
      | sK4 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        | ~ r2_hidden(sK3,X3)
        | sK4 != X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ v3_pre_topc(X3,X0)
                    | ~ r2_hidden(X1,X3)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ v3_pre_topc(X3,sK2)
                  | ~ r2_hidden(X1,X3)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ v3_pre_topc(X3,sK2)
                | ~ r2_hidden(X1,X3)
                | X2 != X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ v3_pre_topc(X3,sK2)
              | ~ r2_hidden(sK3,X3)
              | X2 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ v3_pre_topc(X3,sK2)
            | ~ r2_hidden(sK3,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3))) )
   => ( ! [X3] :
          ( ~ v3_pre_topc(X3,sK2)
          | ~ r2_hidden(sK3,X3)
          | sK4 != X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X1,X3)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X1,X3)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ? [X3] :
                    ( v3_pre_topc(X3,X0)
                    & r2_hidden(X1,X3)
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f134,plain,(
    sP0(sK2,sK3,sK4) ),
    inference(resolution,[],[f133,f96])).

fof(f96,plain,(
    ! [X0] : sP1(X0,sK3,sK2) ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,X0,sK2) ) ),
    inference(global_subsumption,[],[f44,f43,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,X0,sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP1(X0,X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f28,f30,f29])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f133,plain,
    ( ~ sP1(sK4,sK3,sK2)
    | sP0(sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f127,f132])).

fof(f132,plain,(
    ~ v1_xboole_0(a_2_0_yellow_6(sK2,sK3)) ),
    inference(global_subsumption,[],[f46,f45,f44,f43,f131])).

fof(f131,plain,
    ( ~ v1_xboole_0(a_2_0_yellow_6(sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f121,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k9_yellow_6(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_yellow_6)).

% (18343)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f121,plain,
    ( v2_struct_0(k9_yellow_6(sK2,sK3))
    | ~ v1_xboole_0(a_2_0_yellow_6(sK2,sK3)) ),
    inference(global_subsumption,[],[f91,f119])).

fof(f119,plain,
    ( ~ l1_struct_0(k9_yellow_6(sK2,sK3))
    | ~ v1_xboole_0(a_2_0_yellow_6(sK2,sK3))
    | v2_struct_0(k9_yellow_6(sK2,sK3)) ),
    inference(superposition,[],[f77,f116])).

fof(f116,plain,(
    k9_yellow_6(sK2,sK3) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f115,f46])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k9_yellow_6(sK2,X0) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK2,X0))) ) ),
    inference(global_subsumption,[],[f44,f43,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k9_yellow_6(sK2,X0) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK2,X0)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_yellow_6)).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_struct_0(k7_lattice3(k2_yellow_1(X0)))
      | ~ v1_xboole_0(X0)
      | v2_struct_0(k7_lattice3(k2_yellow_1(X0))) ) ),
    inference(superposition,[],[f54,f76])).

fof(f76,plain,(
    ! [X0] : u1_struct_0(k7_lattice3(k2_yellow_1(X0))) = X0 ),
    inference(forward_demodulation,[],[f75,f50])).

fof(f50,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f75,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = u1_struct_0(k7_lattice3(k2_yellow_1(X0))) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f91,plain,(
    l1_struct_0(k9_yellow_6(sK2,sK3)) ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f89,plain,(
    l1_orders_2(k9_yellow_6(sK2,sK3)) ),
    inference(resolution,[],[f88,f46])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | l1_orders_2(k9_yellow_6(sK2,X0)) ) ),
    inference(global_subsumption,[],[f44,f43,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | l1_orders_2(k9_yellow_6(sK2,X0))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | l1_orders_2(k9_yellow_6(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( l1_orders_2(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( l1_orders_2(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => l1_orders_2(k9_yellow_6(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_yellow_6)).

fof(f127,plain,
    ( ~ sP1(sK4,sK3,sK2)
    | sP0(sK2,sK3,sK4)
    | v1_xboole_0(a_2_0_yellow_6(sK2,sK3)) ),
    inference(resolution,[],[f126,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,a_2_0_yellow_6(X0,X1))
      | ~ sP1(X2,X1,X0)
      | sP0(X0,X1,X2)
      | v1_xboole_0(a_2_0_yellow_6(X0,X1)) ) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_yellow_6(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f126,plain,(
    m1_subset_1(sK4,a_2_0_yellow_6(sK2,sK3)) ),
    inference(backward_demodulation,[],[f47,f120])).

fof(f120,plain,(
    u1_struct_0(k9_yellow_6(sK2,sK3)) = a_2_0_yellow_6(sK2,sK3) ),
    inference(superposition,[],[f76,f116])).

fof(f47,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:50:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (18348)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (18348)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (18356)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(global_subsumption,[],[f134,f149,f143])).
% 0.21/0.49  % (18338)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    r2_hidden(sK3,sK4) | ~sP0(sK2,sK3,sK4)),
% 0.21/0.49    inference(superposition,[],[f66,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    sK4 = sK5(sK2,sK3,sK4)),
% 0.21/0.49    inference(resolution,[],[f134,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~v3_pre_topc(X3,X0) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((v3_pre_topc(sK5(X0,X1,X2),X0) & r2_hidden(X1,sK5(X0,X1,X2)) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (v3_pre_topc(X4,X0) & r2_hidden(X1,X4) & X2 = X4 & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK5(X0,X1,X2),X0) & r2_hidden(X1,sK5(X0,X1,X2)) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~v3_pre_topc(X3,X0) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (v3_pre_topc(X4,X0) & r2_hidden(X1,X4) & X2 = X4 & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~v3_pre_topc(X3,X1) | ~r2_hidden(X2,X3) | X0 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X3] : (v3_pre_topc(X3,X1) & r2_hidden(X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X1,X2,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (v3_pre_topc(X3,X1) & r2_hidden(X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,sK5(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~r2_hidden(sK3,sK4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    v3_pre_topc(sK4,sK2)),
% 0.21/0.49    inference(global_subsumption,[],[f134,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    v3_pre_topc(sK4,sK2) | ~sP0(sK2,sK3,sK4)),
% 0.21/0.49    inference(superposition,[],[f67,f136])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v3_pre_topc(sK5(X0,X1,X2),X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~r2_hidden(sK3,sK4) | ~v3_pre_topc(sK4,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.49    inference(global_subsumption,[],[f134,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK2,sK3,sK4)),
% 0.21/0.49    inference(superposition,[],[f64,f136])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(sK3,sK4) | ~v3_pre_topc(sK4,sK2)),
% 0.21/0.49    inference(equality_resolution,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(sK3,X3) | sK4 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ((! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(sK3,X3) | sK4 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f34,f33,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~v3_pre_topc(X3,X0) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(sK3,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ? [X2] : (! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(sK3,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3)))) => (! [X3] : (~v3_pre_topc(X3,sK2) | ~r2_hidden(sK3,X3) | sK4 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~v3_pre_topc(X3,X0) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~v3_pre_topc(X3,X0) | ~r2_hidden(X1,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    sP0(sK2,sK3,sK4)),
% 0.21/0.49    inference(resolution,[],[f133,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (sP1(X0,sK3,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f95,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X1,X0,sK2)) )),
% 0.21/0.49    inference(global_subsumption,[],[f44,f43,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X1,X0,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f69,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    l1_pre_topc(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | sP1(X0,X2,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(definition_folding,[],[f28,f30,f29])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_yellow_6(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_yellow_6(X1,X2)) <=> ? [X3] : (v3_pre_topc(X3,X1) & r2_hidden(X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_yellow_6(X1,X2)) <=> ? [X3] : (v3_pre_topc(X3,X1) & r2_hidden(X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_yellow_6(X1,X2)) <=> ? [X3] : (v3_pre_topc(X3,X1) & r2_hidden(X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v2_pre_topc(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~sP1(sK4,sK3,sK2) | sP0(sK2,sK3,sK4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~v1_xboole_0(a_2_0_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(global_subsumption,[],[f46,f45,f44,f43,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~v1_xboole_0(a_2_0_yellow_6(sK2,sK3)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f121,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_struct_0(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (~v2_struct_0(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (~v2_struct_0(k9_yellow_6(X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_struct_0(k9_yellow_6(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_yellow_6)).
% 0.21/0.49  % (18343)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v2_struct_0(k9_yellow_6(sK2,sK3)) | ~v1_xboole_0(a_2_0_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(global_subsumption,[],[f91,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~l1_struct_0(k9_yellow_6(sK2,sK3)) | ~v1_xboole_0(a_2_0_yellow_6(sK2,sK3)) | v2_struct_0(k9_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(superposition,[],[f77,f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    k9_yellow_6(sK2,sK3) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK2,sK3)))),
% 0.21/0.49    inference(resolution,[],[f115,f46])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | k9_yellow_6(sK2,X0) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK2,X0)))) )),
% 0.21/0.49    inference(global_subsumption,[],[f44,f43,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | k9_yellow_6(sK2,X0) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK2,X0))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f55,f45])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_yellow_6)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(k7_lattice3(k2_yellow_1(X0))) | ~v1_xboole_0(X0) | v2_struct_0(k7_lattice3(k2_yellow_1(X0)))) )),
% 0.21/0.49    inference(superposition,[],[f54,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (u1_struct_0(k7_lattice3(k2_yellow_1(X0))) = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f75,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = u1_struct_0(k7_lattice3(k2_yellow_1(X0)))) )),
% 0.21/0.49    inference(resolution,[],[f53,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(X0) | u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    l1_struct_0(k9_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(resolution,[],[f89,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    l1_orders_2(k9_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(resolution,[],[f88,f46])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | l1_orders_2(k9_yellow_6(sK2,X0))) )),
% 0.21/0.49    inference(global_subsumption,[],[f44,f43,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | l1_orders_2(k9_yellow_6(sK2,X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f61,f45])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | l1_orders_2(k9_yellow_6(X0,X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (l1_orders_2(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (l1_orders_2(k9_yellow_6(X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => l1_orders_2(k9_yellow_6(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_yellow_6)).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ~sP1(sK4,sK3,sK2) | sP0(sK2,sK3,sK4) | v1_xboole_0(a_2_0_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(resolution,[],[f126,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,a_2_0_yellow_6(X0,X1)) | ~sP1(X2,X1,X0) | sP0(X0,X1,X2) | v1_xboole_0(a_2_0_yellow_6(X0,X1))) )),
% 0.21/0.49    inference(resolution,[],[f62,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_yellow_6(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow_6(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_yellow_6(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.49    inference(rectify,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_yellow_6(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_yellow_6(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    m1_subset_1(sK4,a_2_0_yellow_6(sK2,sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f47,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    u1_struct_0(k9_yellow_6(sK2,sK3)) = a_2_0_yellow_6(sK2,sK3)),
% 0.21/0.49    inference(superposition,[],[f76,f116])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18348)------------------------------
% 0.21/0.49  % (18348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18348)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18348)Memory used [KB]: 6268
% 0.21/0.49  % (18348)Time elapsed: 0.059 s
% 0.21/0.49  % (18348)------------------------------
% 0.21/0.49  % (18348)------------------------------
% 0.21/0.49  % (18360)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.49  % (18335)Success in time 0.135 s
%------------------------------------------------------------------------------
