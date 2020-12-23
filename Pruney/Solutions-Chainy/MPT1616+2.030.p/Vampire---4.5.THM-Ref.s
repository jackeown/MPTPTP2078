%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 339 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          :  309 (1328 expanded)
%              Number of equality atoms :   38 ( 179 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f476])).

fof(f476,plain,(
    u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(superposition,[],[f54,f471])).

fof(f471,plain,(
    u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) ),
    inference(resolution,[],[f465,f372])).

fof(f372,plain,(
    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f324,f342])).

fof(f342,plain,(
    u1_struct_0(sK1) = k3_tarski(u1_pre_topc(sK1)) ),
    inference(resolution,[],[f341,f53])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( u1_struct_0(sK1) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK1) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f341,plain,
    ( ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) = k3_tarski(u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f340,f203])).

fof(f203,plain,(
    k3_tarski(u1_pre_topc(sK1)) = k5_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f124,f53])).

fof(f124,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | k3_tarski(u1_pre_topc(X2)) = k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

% (18926)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f340,plain,
    ( u1_struct_0(sK1) = k5_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f339,f52])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f339,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | u1_struct_0(X0) = k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f268,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
            & r1_tarski(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f268,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(resolution,[],[f157,f84])).

% (18919)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f84,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f78,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f157,plain,(
    ! [X2] :
      ( ~ m1_setfam_1(u1_pre_topc(X2),u1_struct_0(X2))
      | u1_struct_0(X2) = k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f73,f57])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f324,plain,(
    r2_hidden(k3_tarski(u1_pre_topc(sK1)),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f323,f129])).

fof(f129,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(forward_demodulation,[],[f125,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

% (18923)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f125,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ) ),
    inference(resolution,[],[f100,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK5(k1_zfmisc_1(X0),X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f99,f55])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1)
      | r1_tarski(sK5(k1_zfmisc_1(X0),X1),X0) ) ),
    inference(resolution,[],[f75,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f70,f55])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f323,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | r2_hidden(k3_tarski(u1_pre_topc(sK1)),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f322,f53])).

fof(f322,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | r2_hidden(k3_tarski(u1_pre_topc(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f321,f203])).

fof(f321,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1)),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f290,f57])).

fof(f290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | r2_hidden(k5_setfam_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1))
      | ~ r1_tarski(X0,u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f208,f53])).

fof(f208,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | r2_hidden(k5_setfam_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1))
      | ~ r1_tarski(X0,u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f65,f52])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f465,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) ) ),
    inference(resolution,[],[f464,f129])).

fof(f464,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_pre_topc(sK1))
      | ~ r2_hidden(X0,X1)
      | u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) ) ),
    inference(resolution,[],[f374,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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

fof(f374,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK1)))
      | u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(backward_demodulation,[],[f331,f342])).

fof(f331,plain,(
    ! [X0,X1] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) = k3_tarski(u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f326,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f326,plain,
    ( v1_xboole_0(u1_pre_topc(sK1))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) = k3_tarski(u1_pre_topc(sK1)) ),
    inference(resolution,[],[f324,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (18919)Refutation not found, incomplete strategy% (18919)------------------------------
% (18919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f20,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f54,plain,(
    u1_struct_0(sK1) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (18921)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (18929)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (18916)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (18921)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (18915)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f477,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f476])).
% 0.22/0.51  fof(f476,plain,(
% 0.22/0.51    u1_struct_0(sK1) != u1_struct_0(sK1)),
% 0.22/0.51    inference(superposition,[],[f54,f471])).
% 0.22/0.51  fof(f471,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))),
% 0.22/0.51    inference(resolution,[],[f465,f372])).
% 0.22/0.51  fof(f372,plain,(
% 0.22/0.51    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.51    inference(backward_demodulation,[],[f324,f342])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k3_tarski(u1_pre_topc(sK1))),
% 0.22/0.51    inference(resolution,[],[f341,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    u1_struct_0(sK1) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK1) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | u1_struct_0(sK1) = k3_tarski(u1_pre_topc(sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f340,f203])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    k3_tarski(u1_pre_topc(sK1)) = k5_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.51    inference(resolution,[],[f124,f53])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X2] : (~l1_pre_topc(X2) | k3_tarski(u1_pre_topc(X2)) = k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2))) )),
% 0.22/0.51    inference(resolution,[],[f72,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.22/0.51  % (18926)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k5_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.51    inference(resolution,[],[f339,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v2_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | u1_struct_0(X0) = k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f338])).
% 0.22/0.51  fof(f338,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(resolution,[],[f268,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(rectify,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(definition_folding,[],[f23,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.52    inference(rectify,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 0.22/0.52    inference(resolution,[],[f157,f84])).
% 0.22/0.52  % (18919)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_setfam_1(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f78,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X2] : (~m1_setfam_1(u1_pre_topc(X2),u1_struct_0(X2)) | u1_struct_0(X2) = k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2)) | ~l1_pre_topc(X2)) )),
% 0.22/0.52    inference(resolution,[],[f73,f57])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(nnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.22/0.52  fof(f324,plain,(
% 0.22/0.52    r2_hidden(k3_tarski(u1_pre_topc(sK1)),u1_pre_topc(sK1))),
% 0.22/0.52    inference(resolution,[],[f323,f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f125,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  % (18923)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)) )),
% 0.22/0.52    inference(resolution,[],[f100,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(sK5(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(sK5(k1_zfmisc_1(X0),X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f99,f55])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) | r1_tarski(sK5(k1_zfmisc_1(X0),X1),X0)) )),
% 0.22/0.52    inference(resolution,[],[f75,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.22/0.52    inference(superposition,[],[f70,f55])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f323,plain,(
% 0.22/0.52    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | r2_hidden(k3_tarski(u1_pre_topc(sK1)),u1_pre_topc(sK1))),
% 0.22/0.52    inference(resolution,[],[f322,f53])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | r2_hidden(k3_tarski(u1_pre_topc(sK1)),u1_pre_topc(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f321,f203])).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    r2_hidden(k5_setfam_1(u1_struct_0(sK1),u1_pre_topc(sK1)),u1_pre_topc(sK1)) | ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.52    inference(resolution,[],[f290,f57])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(k5_setfam_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1)) | ~r1_tarski(X0,u1_pre_topc(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f208,f53])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(k5_setfam_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1)) | ~r1_tarski(X0,u1_pre_topc(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f65,f52])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f465,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK1)) | u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))) )),
% 0.22/0.52    inference(resolution,[],[f464,f129])).
% 0.22/0.52  fof(f464,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,u1_pre_topc(sK1)) | ~r2_hidden(X0,X1) | u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))) )),
% 0.22/0.52    inference(resolution,[],[f374,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f374,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK1))) | u1_struct_0(sK1) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f331,f342])).
% 0.22/0.52  fof(f331,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) = k3_tarski(u1_pre_topc(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK1))) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f326,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.52  fof(f326,plain,(
% 0.22/0.52    v1_xboole_0(u1_pre_topc(sK1)) | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1))) = k3_tarski(u1_pre_topc(sK1))),
% 0.22/0.52    inference(resolution,[],[f324,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  % (18919)Refutation not found, incomplete strategy% (18919)------------------------------
% 0.22/0.52  % (18919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    u1_struct_0(sK1) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (18921)------------------------------
% 0.22/0.52  % (18921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18921)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (18921)Memory used [KB]: 1918
% 0.22/0.52  % (18921)Time elapsed: 0.095 s
% 0.22/0.52  % (18921)------------------------------
% 0.22/0.52  % (18921)------------------------------
% 0.22/0.52  % (18928)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (18912)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (18911)Success in time 0.157 s
%------------------------------------------------------------------------------
