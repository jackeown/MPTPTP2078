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
% DateTime   : Thu Dec  3 13:13:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 218 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  259 (1118 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f195,f202])).

fof(f202,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f200,f163])).

fof(f163,plain,(
    ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f161,f37])).

fof(f37,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v1_tops_2(sK3,sK2)
    & v1_tops_2(sK4,sK2)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(X1,X0)
                & v1_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,sK2)
              & v1_tops_2(X2,sK2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(X1,sK2)
            & v1_tops_2(X2,sK2)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(sK3,sK2)
          & v1_tops_2(X2,sK2)
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(sK3,sK2)
        & v1_tops_2(X2,sK2)
        & r1_tarski(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v1_tops_2(sK3,sK2)
      & v1_tops_2(sK4,sK2)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v1_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f161,plain,
    ( ~ sP0(sK2,sK3)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f159,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_tops_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v1_tops_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_tops_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( ( v1_tops_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_tops_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( v1_tops_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f159,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f156,f32])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f156,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f20,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v3_pre_topc(X2,X0)
          | ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f200,plain,
    ( ! [X0] : sP0(X0,sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v3_pre_topc(sK5(X0,X1),X0)
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f71,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_4
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f195,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f193,f163])).

fof(f193,plain,
    ( sP0(sK2,sK3)
    | spl6_7 ),
    inference(resolution,[],[f191,f166])).

fof(f166,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f165,f36])).

fof(f36,plain,(
    v1_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f165,plain,
    ( ~ v1_tops_2(sK4,sK2)
    | sP0(sK2,sK4) ),
    inference(resolution,[],[f160,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v1_tops_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f160,plain,(
    sP1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f157,f32])).

fof(f157,plain,
    ( sP1(sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f191,plain,
    ( ! [X2] :
        ( ~ sP0(X2,sK4)
        | sP0(X2,sK3) )
    | spl6_7 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X2] :
        ( ~ sP0(X2,sK4)
        | sP0(X2,sK3)
        | sP0(X2,sK3) )
    | spl6_7 ),
    inference(resolution,[],[f181,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,sK3),sK4)
        | sP0(X0,sK3) )
    | spl6_7 ),
    inference(subsumption_resolution,[],[f111,f85])).

fof(f85,plain,
    ( ~ v1_xboole_0(sK4)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_7
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f111,plain,(
    ! [X0] :
      ( sP0(X0,sK3)
      | v1_xboole_0(sK4)
      | r2_hidden(sK5(X0,sK3),sK4) ) ),
    inference(resolution,[],[f110,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0,sK3),sK4)
      | sP0(X0,sK3) ) ),
    inference(resolution,[],[f109,f42])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | m1_subset_1(X0,sK4) ) ),
    inference(resolution,[],[f91,f35])).

fof(f35,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r2_hidden(X2,X4)
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X2)
      | ~ sP0(X0,X2)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f177,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X2)
      | v3_pre_topc(sK5(X0,X1),X0)
      | ~ sP0(X0,X2)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,X1)
      | v3_pre_topc(X3,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,
    ( ~ spl6_7
    | spl6_4 ),
    inference(avatar_split_clause,[],[f81,f70,f83])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f48,f46])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (16355)WARNING: option uwaf not known.
% 0.21/0.47  % (16352)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (16355)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.47  % (16352)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f86,f195,f202])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    ~spl6_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    $false | ~spl6_4),
% 0.21/0.47    inference(resolution,[],[f200,f163])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ~sP0(sK2,sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f161,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~v1_tops_2(sK3,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ((~v1_tops_2(sK3,sK2) & v1_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f24,f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(X1,sK2) & v1_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~v1_tops_2(X1,sK2) & v1_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (? [X2] : (~v1_tops_2(sK3,sK2) & v1_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X2] : (~v1_tops_2(sK3,sK2) & v1_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (~v1_tops_2(sK3,sK2) & v1_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(X1,X0) & (v1_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ~sP0(sK2,sK3) | v1_tops_2(sK3,sK2)),
% 0.21/0.47    inference(resolution,[],[f159,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v1_tops_2(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : (((v1_tops_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v1_tops_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.47    inference(rectify,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X1,X0] : (((v1_tops_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v1_tops_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X1,X0] : ((v1_tops_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    sP1(sK3,sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f156,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    l1_pre_topc(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    sP1(sK3,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.47    inference(resolution,[],[f44,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | sP1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(definition_folding,[],[f12,f20,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    ( ! [X0] : (sP0(X0,sK3)) ) | ~spl6_4),
% 0.21/0.47    inference(resolution,[],[f71,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | (~v3_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f19])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl6_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl6_4 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl6_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    $false | spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f193,f163])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    sP0(sK2,sK3) | spl6_7),
% 0.21/0.48    inference(resolution,[],[f191,f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    sP0(sK2,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v1_tops_2(sK4,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~v1_tops_2(sK4,sK2) | sP0(sK2,sK4)),
% 0.21/0.48    inference(resolution,[],[f160,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP1(X0,X1) | ~v1_tops_2(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    sP1(sK4,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f32])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    sP1(sK4,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(resolution,[],[f44,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X2] : (~sP0(X2,sK4) | sP0(X2,sK3)) ) | spl6_7),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ( ! [X2] : (~sP0(X2,sK4) | sP0(X2,sK3) | sP0(X2,sK3)) ) | spl6_7),
% 0.21/0.48    inference(resolution,[],[f181,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK5(X0,sK3),sK4) | sP0(X0,sK3)) ) | spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v1_xboole_0(sK4) | spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl6_7 <=> v1_xboole_0(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(X0,sK3) | v1_xboole_0(sK4) | r2_hidden(sK5(X0,sK3),sK4)) )),
% 0.21/0.48    inference(resolution,[],[f110,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK5(X0,sK3),sK4) | sP0(X0,sK3)) )),
% 0.21/0.48    inference(resolution,[],[f109,f42])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK3) | m1_subset_1(X0,sK4)) )),
% 0.21/0.48    inference(resolution,[],[f91,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    r1_tarski(sK3,sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | ~r2_hidden(X2,X4) | m1_subset_1(X2,X3)) )),
% 0.21/0.48    inference(resolution,[],[f47,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1),X2) | ~sP0(X0,X2) | sP0(X0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_pre_topc(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1),X2) | v3_pre_topc(sK5(X0,X1),X0) | ~sP0(X0,X2) | sP0(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f40,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,X1) | v3_pre_topc(X3,X0) | ~sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~spl6_7 | spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f70,f83])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(sK4)) )),
% 0.21/0.48    inference(resolution,[],[f68,f35])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | ~r2_hidden(X3,X4) | ~v1_xboole_0(X2)) )),
% 0.21/0.48    inference(resolution,[],[f48,f46])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16352)------------------------------
% 0.21/0.48  % (16352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16352)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16352)Memory used [KB]: 5373
% 0.21/0.48  % (16352)Time elapsed: 0.066 s
% 0.21/0.48  % (16352)------------------------------
% 0.21/0.48  % (16352)------------------------------
% 0.21/0.48  % (16344)Success in time 0.122 s
%------------------------------------------------------------------------------
