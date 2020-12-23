%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 192 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  380 ( 882 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f578,plain,(
    $false ),
    inference(subsumption_resolution,[],[f577,f56])).

fof(f56,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
    & v1_tops_2(sK7,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f11,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
            & v1_tops_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),X1),sK6)
          & v1_tops_2(X1,sK6)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),X1),sK6)
        & v1_tops_2(X1,sK6)
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
   => ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
      & v1_tops_2(sK7,sK6)
      & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

fof(f577,plain,(
    ~ l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f576,f59])).

fof(f59,plain,(
    ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f576,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f575,f95])).

fof(f95,plain,(
    sP0(sK6) ),
    inference(resolution,[],[f93,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ( sP1(X0)
        & sP0(X0)
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f93,plain,(
    sP2(sK6) ),
    inference(subsumption_resolution,[],[f92,f55])).

% (19330)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
fof(f55,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,
    ( ~ v2_pre_topc(sK6)
    | sP2(sK6) ),
    inference(resolution,[],[f61,f91])).

fof(f91,plain,(
    sP3(sK6) ),
    inference(resolution,[],[f77,f56])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f14,f24,f23,f22,f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X3] :
          ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          | ~ r1_tarski(X3,u1_pre_topc(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f61,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | ~ v2_pre_topc(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f575,plain,
    ( ~ sP0(sK6)
    | v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f571,f293])).

fof(f293,plain,(
    r1_tarski(sK7,u1_pre_topc(sK6)) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( r1_tarski(sK7,u1_pre_topc(sK6))
    | r1_tarski(sK7,u1_pre_topc(sK6)) ),
    inference(resolution,[],[f289,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK12(X0,X1),X1)
          & r2_hidden(sK12(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK12(X0,X1),X1)
        & r2_hidden(sK12(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f289,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK12(X2,u1_pre_topc(sK6)),sK7)
      | r1_tarski(X2,u1_pre_topc(sK6)) ) ),
    inference(subsumption_resolution,[],[f179,f232])).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | v3_pre_topc(X0,sK6) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK6)
      | ~ r2_hidden(X0,sK7)
      | ~ r2_hidden(X0,sK7) ) ),
    inference(resolution,[],[f206,f131])).

fof(f131,plain,(
    sP4(sK6,sK7) ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f58,plain,(
    v1_tops_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f130,plain,
    ( ~ v1_tops_2(sK7,sK6)
    | sP4(sK6,sK7) ),
    inference(resolution,[],[f128,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | ~ v1_tops_2(X0,X1)
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_tops_2(X0,X1)
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | ~ v1_tops_2(X0,X1) ) )
      | ~ sP5(X0,X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ( ( v1_tops_2(X1,X0)
          | ~ sP4(X0,X1) )
        & ( sP4(X0,X1)
          | ~ v1_tops_2(X1,X0) ) )
      | ~ sP5(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( v1_tops_2(X1,X0)
      <=> sP4(X0,X1) )
      | ~ sP5(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f128,plain,(
    sP5(sK7,sK6) ),
    inference(subsumption_resolution,[],[f125,f56])).

fof(f125,plain,
    ( sP5(sK7,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP5(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP5(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ! [X2] :
          ( v3_pre_topc(X2,X0)
          | ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ sP4(sK6,X1)
      | v3_pre_topc(X0,sK6)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK7) ) ),
    inference(resolution,[],[f82,f105])).

fof(f105,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ r2_hidden(X2,sK7) ) ),
    inference(resolution,[],[f90,f57])).

% (19341)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,X1)
      | v3_pre_topc(X3,X0)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ( ~ v3_pre_topc(sK11(X0,X1),X0)
          & r2_hidden(sK11(X0,X1),X1)
          & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK11(X0,X1),X0)
        & r2_hidden(sK11(X0,X1),X1)
        & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f179,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(sK12(X2,u1_pre_topc(sK6)),sK6)
      | ~ r2_hidden(sK12(X2,u1_pre_topc(sK6)),sK7)
      | r1_tarski(X2,u1_pre_topc(sK6)) ) ),
    inference(resolution,[],[f174,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK12(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f174,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_pre_topc(sK6))
      | ~ v3_pre_topc(X0,sK6)
      | ~ r2_hidden(X0,sK7) ) ),
    inference(subsumption_resolution,[],[f167,f56])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK6)
      | r2_hidden(X0,u1_pre_topc(sK6))
      | ~ l1_pre_topc(sK6)
      | ~ r2_hidden(X0,sK7) ) ),
    inference(resolution,[],[f78,f105])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f571,plain,
    ( ~ r1_tarski(sK7,u1_pre_topc(sK6))
    | ~ sP0(sK6)
    | v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f328,f57])).

fof(f328,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ r1_tarski(X1,u1_pre_topc(X2))
      | ~ sP0(X2)
      | v3_pre_topc(k5_setfam_1(u1_struct_0(X2),X1),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f73,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f79,f104])).

% (19338)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,u1_pre_topc(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
          & r1_tarski(sK10(X0),u1_pre_topc(X0))
          & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X2] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
            | ~ r1_tarski(X2,u1_pre_topc(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
        & r1_tarski(sK10(X0),u1_pre_topc(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            & r1_tarski(X1,u1_pre_topc(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X2] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
            | ~ r1_tarski(X2,u1_pre_topc(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (19334)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.45  % (19328)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.46  % (19344)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.47  % (19327)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (19334)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f578,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f577,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    l1_pre_topc(sK6)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    (~v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) & v1_tops_2(sK7,sK6) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f11,f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) & v1_tops_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),X1),sK6) & v1_tops_2(X1,sK6) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X1] : (~v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),X1),sK6) & v1_tops_2(X1,sK6) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) => (~v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) & v1_tops_2(sK7,sK6) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) & v1_tops_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).
% 0.21/0.49  fof(f577,plain,(
% 0.21/0.49    ~l1_pre_topc(sK6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f576,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f576,plain,(
% 0.21/0.49    v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) | ~l1_pre_topc(sK6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f575,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sP0(sK6)),
% 0.21/0.49    inference(resolution,[],[f93,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0) | sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : ((sP2(X0) | ~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : ((sP2(X0) | (~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (sP2(X0) <=> (sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    sP2(sK6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f55])).
% 0.21/0.49  % (19330)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v2_pre_topc(sK6)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~v2_pre_topc(sK6) | sP2(sK6)),
% 0.21/0.49    inference(resolution,[],[f61,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    sP3(sK6)),
% 0.21/0.49    inference(resolution,[],[f77,f56])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | sP3(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (sP3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(definition_folding,[],[f14,f24,f23,f22,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (sP0(X0) <=> ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (sP1(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : ((v2_pre_topc(X0) <=> sP2(X0)) | ~sP3(X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.49    inference(rectify,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (~sP3(X0) | ~v2_pre_topc(X0) | sP2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (((v2_pre_topc(X0) | ~sP2(X0)) & (sP2(X0) | ~v2_pre_topc(X0))) | ~sP3(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f575,plain,(
% 0.21/0.49    ~sP0(sK6) | v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) | ~l1_pre_topc(sK6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f571,f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    r1_tarski(sK7,u1_pre_topc(sK6))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f290])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    r1_tarski(sK7,u1_pre_topc(sK6)) | r1_tarski(sK7,u1_pre_topc(sK6))),
% 0.21/0.49    inference(resolution,[],[f289,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK12(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK12(X0,X1),X1) & r2_hidden(sK12(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f52,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK12(X0,X1),X1) & r2_hidden(sK12(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(sK12(X2,u1_pre_topc(sK6)),sK7) | r1_tarski(X2,u1_pre_topc(sK6))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f179,f232])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK7) | v3_pre_topc(X0,sK6)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f229])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(X0,sK6) | ~r2_hidden(X0,sK7) | ~r2_hidden(X0,sK7)) )),
% 0.21/0.49    inference(resolution,[],[f206,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sP4(sK6,sK7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v1_tops_2(sK7,sK6)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~v1_tops_2(sK7,sK6) | sP4(sK6,sK7)),
% 0.21/0.49    inference(resolution,[],[f128,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP5(X0,X1) | ~v1_tops_2(X0,X1) | sP4(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1] : (((v1_tops_2(X0,X1) | ~sP4(X1,X0)) & (sP4(X1,X0) | ~v1_tops_2(X0,X1))) | ~sP5(X0,X1))),
% 0.21/0.49    inference(rectify,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X1,X0] : (((v1_tops_2(X1,X0) | ~sP4(X0,X1)) & (sP4(X0,X1) | ~v1_tops_2(X1,X0))) | ~sP5(X1,X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X1,X0] : ((v1_tops_2(X1,X0) <=> sP4(X0,X1)) | ~sP5(X1,X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    sP5(sK7,sK6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f56])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    sP5(sK7,sK6) | ~l1_pre_topc(sK6)),
% 0.21/0.49    inference(resolution,[],[f86,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | sP5(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (sP5(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(definition_folding,[],[f17,f27,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (sP4(X0,X1) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP4(sK6,X1) | v3_pre_topc(X0,sK6) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,sK7)) )),
% 0.21/0.49    inference(resolution,[],[f82,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X2,sK7)) )),
% 0.21/0.49    inference(resolution,[],[f90,f57])).
% 0.21/0.49  % (19341)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,X1) | v3_pre_topc(X3,X0) | ~sP4(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP4(X0,X1) | (~v3_pre_topc(sK11(X0,X1),X0) & r2_hidden(sK11(X0,X1),X1) & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK11(X0,X1),X0) & r2_hidden(sK11(X0,X1),X1) & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X2] : (~v3_pre_topc(sK12(X2,u1_pre_topc(sK6)),sK6) | ~r2_hidden(sK12(X2,u1_pre_topc(sK6)),sK7) | r1_tarski(X2,u1_pre_topc(sK6))) )),
% 0.21/0.49    inference(resolution,[],[f174,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK12(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,u1_pre_topc(sK6)) | ~v3_pre_topc(X0,sK6) | ~r2_hidden(X0,sK7)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f167,f56])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK6) | r2_hidden(X0,u1_pre_topc(sK6)) | ~l1_pre_topc(sK6) | ~r2_hidden(X0,sK7)) )),
% 0.21/0.49    inference(resolution,[],[f78,f105])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.49  fof(f571,plain,(
% 0.21/0.49    ~r1_tarski(sK7,u1_pre_topc(sK6)) | ~sP0(sK6) | v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) | ~l1_pre_topc(sK6)),
% 0.21/0.49    inference(resolution,[],[f328,f57])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~r1_tarski(X1,u1_pre_topc(X2)) | ~sP0(X2) | v3_pre_topc(k5_setfam_1(u1_struct_0(X2),X1),X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.49    inference(resolution,[],[f73,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f104])).
% 0.21/0.49  % (19338)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f90,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f41,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X0)))),
% 0.21/0.49    inference(rectify,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19334)------------------------------
% 0.21/0.49  % (19334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19334)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19334)Memory used [KB]: 5628
% 0.21/0.49  % (19334)Time elapsed: 0.063 s
% 0.21/0.49  % (19334)------------------------------
% 0.21/0.49  % (19334)------------------------------
% 0.21/0.49  % (19326)Success in time 0.134 s
%------------------------------------------------------------------------------
