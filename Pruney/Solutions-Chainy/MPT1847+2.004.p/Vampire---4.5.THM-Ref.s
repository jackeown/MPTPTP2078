%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:34 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  160 (2152 expanded)
%              Number of leaves         :   24 ( 769 expanded)
%              Depth                    :   28
%              Number of atoms          :  506 (11636 expanded)
%              Number of equality atoms :   69 (1983 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3574,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3436,f473])).

fof(f473,plain,(
    ~ v1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6)) ),
    inference(backward_demodulation,[],[f459,f463])).

fof(f463,plain,(
    u1_struct_0(sK8) = u1_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f462,f173])).

fof(f173,plain,(
    m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f167,f68])).

fof(f68,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ v1_tex_2(sK8,sK6)
    & v1_tex_2(sK7,sK6)
    & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
    & m1_pre_topc(sK8,sK6)
    & m1_pre_topc(sK7,sK6)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f19,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK6)
              & v1_tex_2(X1,sK6)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK6) )
          & m1_pre_topc(X1,sK6) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK6)
            & v1_tex_2(X1,sK6)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK6) )
        & m1_pre_topc(X1,sK6) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK6)
          & v1_tex_2(sK7,sK6)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
          & m1_pre_topc(X2,sK6) )
      & m1_pre_topc(sK7,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK6)
        & v1_tex_2(sK7,sK6)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
        & m1_pre_topc(X2,sK6) )
   => ( ~ v1_tex_2(sK8,sK6)
      & v1_tex_2(sK7,sK6)
      & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
      & m1_pre_topc(sK8,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f167,plain,
    ( m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f70,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f70,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f462,plain,
    ( u1_struct_0(sK8) = u1_struct_0(sK6)
    | ~ m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[],[f459,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f459,plain,(
    ~ v1_subset_1(u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f458,f205])).

fof(f205,plain,(
    ~ sP4(sK6,sK8) ),
    inference(subsumption_resolution,[],[f204,f73])).

fof(f73,plain,(
    ~ v1_tex_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f204,plain,
    ( v1_tex_2(sK8,sK6)
    | ~ sP4(sK6,sK8) ),
    inference(resolution,[],[f172,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X0,X1)
      | ~ sP4(X1,X0)
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_tex_2(X0,X1)
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | ~ v1_tex_2(X0,X1) ) )
      | ~ sP5(X0,X1) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ( ( v1_tex_2(X1,X0)
          | ~ sP4(X0,X1) )
        & ( sP4(X0,X1)
          | ~ v1_tex_2(X1,X0) ) )
      | ~ sP5(X1,X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ( v1_tex_2(X1,X0)
      <=> sP4(X0,X1) )
      | ~ sP5(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f172,plain,(
    sP5(sK8,sK6) ),
    inference(subsumption_resolution,[],[f166,f68])).

fof(f166,plain,
    ( sP5(sK8,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f70,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP5(X1,X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f27,f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ! [X2] :
          ( v1_subset_1(X2,u1_struct_0(X0))
          | u1_struct_0(X1) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f458,plain,
    ( ~ v1_subset_1(u1_struct_0(sK8),u1_struct_0(sK6))
    | sP4(sK6,sK8) ),
    inference(superposition,[],[f103,f209])).

fof(f209,plain,(
    u1_struct_0(sK8) = sK11(sK6,sK8) ),
    inference(resolution,[],[f205,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | u1_struct_0(X1) = sK11(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ( ~ v1_subset_1(sK11(X0,X1),u1_struct_0(X0))
          & u1_struct_0(X1) = sK11(X0,X1)
          & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v1_subset_1(X3,u1_struct_0(X0))
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK11(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK11(X0,X1)
        & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ~ v1_subset_1(X2,u1_struct_0(X0))
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v1_subset_1(X3,u1_struct_0(X0))
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ~ v1_subset_1(X2,u1_struct_0(X0))
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v1_subset_1(X2,u1_struct_0(X0))
            | u1_struct_0(X1) != X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ v1_subset_1(sK11(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f3436,plain,(
    v1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6)) ),
    inference(backward_demodulation,[],[f291,f3424])).

fof(f3424,plain,(
    u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f3422,f337])).

fof(f337,plain,(
    r1_tarski(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f336,f164])).

fof(f164,plain,(
    u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(resolution,[],[f149,f77])).

fof(f77,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f149,plain,(
    l1_struct_0(sK7) ),
    inference(resolution,[],[f146,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f146,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f140,f68])).

fof(f140,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f69,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f69,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f336,plain,(
    r1_tarski(k2_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f240,f148])).

fof(f148,plain,(
    u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(resolution,[],[f122,f77])).

fof(f122,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f68,f78])).

fof(f240,plain,(
    r1_tarski(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(resolution,[],[f224,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ~ sP1(X1,X0,sK9(X0,X1))
          & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP1(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP1(X1,X0,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ sP1(X1,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP1(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ~ sP1(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ~ sP1(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( ! [X2] :
            ( sP1(X0,X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f224,plain,(
    sP2(sK7,sK6) ),
    inference(subsumption_resolution,[],[f222,f69])).

fof(f222,plain,
    ( sP2(sK7,sK6)
    | ~ m1_pre_topc(sK7,sK6) ),
    inference(resolution,[],[f214,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP2(X1,X0) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f214,plain,(
    sP3(sK6,sK7) ),
    inference(resolution,[],[f127,f146])).

fof(f127,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | sP3(sK6,X4) ) ),
    inference(resolution,[],[f68,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f37,f36,f35,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & r2_hidden(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> sP0(X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f3422,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6)
    | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f3404,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3404,plain,(
    r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(backward_demodulation,[],[f2586,f3382])).

fof(f3382,plain,(
    u1_struct_0(sK6) = k2_struct_0(k1_pre_topc(sK8,u1_struct_0(sK6))) ),
    inference(resolution,[],[f3328,f465])).

fof(f465,plain,(
    m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(backward_demodulation,[],[f173,f463])).

fof(f3328,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK6)))
      | k2_struct_0(k1_pre_topc(sK8,X13)) = X13 ) ),
    inference(subsumption_resolution,[],[f3327,f1461])).

fof(f1461,plain,(
    ! [X11] :
      ( m1_pre_topc(k1_pre_topc(sK8,X11),sK8)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(forward_demodulation,[],[f189,f463])).

fof(f189,plain,(
    ! [X11] :
      ( m1_pre_topc(k1_pre_topc(sK8,X11),sK8)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK8))) ) ),
    inference(resolution,[],[f174,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f174,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f168,f68])).

fof(f168,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f70,f96])).

fof(f3327,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK6)))
      | k2_struct_0(k1_pre_topc(sK8,X13)) = X13
      | ~ m1_pre_topc(k1_pre_topc(sK8,X13),sK8) ) ),
    inference(subsumption_resolution,[],[f3326,f1199])).

fof(f1199,plain,(
    ! [X10] :
      ( v1_pre_topc(k1_pre_topc(sK8,X10))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(forward_demodulation,[],[f188,f463])).

fof(f188,plain,(
    ! [X10] :
      ( v1_pre_topc(k1_pre_topc(sK8,X10))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK8))) ) ),
    inference(resolution,[],[f174,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3326,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK6)))
      | k2_struct_0(k1_pre_topc(sK8,X13)) = X13
      | ~ m1_pre_topc(k1_pre_topc(sK8,X13),sK8)
      | ~ v1_pre_topc(k1_pre_topc(sK8,X13)) ) ),
    inference(forward_demodulation,[],[f191,f463])).

fof(f191,plain,(
    ! [X13] :
      ( k2_struct_0(k1_pre_topc(sK8,X13)) = X13
      | ~ m1_pre_topc(k1_pre_topc(sK8,X13),sK8)
      | ~ v1_pre_topc(k1_pre_topc(sK8,X13))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK8))) ) ),
    inference(resolution,[],[f174,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f2586,plain,(
    r1_tarski(k2_struct_0(k1_pre_topc(sK8,u1_struct_0(sK6))),u1_struct_0(sK7)) ),
    inference(resolution,[],[f2583,f313])).

fof(f313,plain,(
    ! [X1] :
      ( ~ sP2(X1,sK7)
      | r1_tarski(k2_struct_0(X1),u1_struct_0(sK7)) ) ),
    inference(superposition,[],[f83,f164])).

fof(f2583,plain,(
    sP2(k1_pre_topc(sK8,u1_struct_0(sK6)),sK7) ),
    inference(subsumption_resolution,[],[f2575,f1624])).

fof(f1624,plain,(
    sP3(sK7,k1_pre_topc(sK8,u1_struct_0(sK6))) ),
    inference(resolution,[],[f1569,f154])).

fof(f154,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | sP3(sK7,X4) ) ),
    inference(resolution,[],[f146,f95])).

fof(f1569,plain,(
    l1_pre_topc(k1_pre_topc(sK8,u1_struct_0(sK6))) ),
    inference(resolution,[],[f1521,f465])).

fof(f1521,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | l1_pre_topc(k1_pre_topc(sK8,X3)) ) ),
    inference(forward_demodulation,[],[f307,f463])).

fof(f307,plain,(
    ! [X3] :
      ( l1_pre_topc(k1_pre_topc(sK8,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) ) ),
    inference(subsumption_resolution,[],[f304,f174])).

fof(f304,plain,(
    ! [X3] :
      ( l1_pre_topc(k1_pre_topc(sK8,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))
      | ~ l1_pre_topc(sK8) ) ),
    inference(resolution,[],[f184,f111])).

fof(f184,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK8)
      | l1_pre_topc(X6) ) ),
    inference(resolution,[],[f174,f96])).

fof(f2575,plain,
    ( sP2(k1_pre_topc(sK8,u1_struct_0(sK6)),sK7)
    | ~ sP3(sK7,k1_pre_topc(sK8,u1_struct_0(sK6))) ),
    inference(resolution,[],[f2532,f763])).

fof(f763,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(X5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))
      | sP2(X5,sK7)
      | ~ sP3(sK7,X5) ) ),
    inference(resolution,[],[f525,f81])).

fof(f525,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK7)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) ) ),
    inference(subsumption_resolution,[],[f522,f146])).

fof(f522,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))
      | m1_pre_topc(X0,sK7)
      | ~ l1_pre_topc(sK7) ) ),
    inference(superposition,[],[f107,f464])).

fof(f464,plain,(
    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)) ),
    inference(backward_demodulation,[],[f71,f463])).

fof(f71,plain,(
    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f2532,plain,(
    m1_pre_topc(k1_pre_topc(sK8,u1_struct_0(sK6)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) ),
    inference(resolution,[],[f899,f465])).

fof(f899,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
      | m1_pre_topc(k1_pre_topc(sK8,X4),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) ) ),
    inference(forward_demodulation,[],[f898,f463])).

fof(f898,plain,(
    ! [X4] :
      ( m1_pre_topc(k1_pre_topc(sK8,X4),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK8))) ) ),
    inference(subsumption_resolution,[],[f893,f174])).

fof(f893,plain,(
    ! [X4] :
      ( m1_pre_topc(k1_pre_topc(sK8,X4),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK8)))
      | ~ l1_pre_topc(sK8) ) ),
    inference(resolution,[],[f863,f111])).

fof(f863,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK8)
      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) ) ),
    inference(forward_demodulation,[],[f862,f464])).

fof(f862,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | ~ m1_pre_topc(X1,sK8) ) ),
    inference(subsumption_resolution,[],[f201,f184])).

fof(f201,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | ~ m1_pre_topc(X1,sK8)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f198,f174])).

fof(f198,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | ~ m1_pre_topc(X1,sK8)
      | ~ l1_pre_topc(sK8)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f79,f71])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f291,plain,(
    v1_subset_1(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f284,f196])).

fof(f196,plain,(
    sP4(sK6,sK7) ),
    inference(subsumption_resolution,[],[f194,f72])).

fof(f72,plain,(
    v1_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f194,plain,
    ( sP4(sK6,sK7)
    | ~ v1_tex_2(sK7,sK6) ),
    inference(resolution,[],[f144,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ v1_tex_2(X0,X1)
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f144,plain,(
    sP5(sK7,sK6) ),
    inference(subsumption_resolution,[],[f138,f68])).

fof(f138,plain,
    ( sP5(sK7,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f69,f104])).

fof(f284,plain,
    ( v1_subset_1(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ sP4(sK6,sK7) ),
    inference(resolution,[],[f145,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP4(X0,X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f145,plain,(
    m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f139,f68])).

fof(f139,plain,
    ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f69,f97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (6182)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (6188)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (6182)Refutation not found, incomplete strategy% (6182)------------------------------
% 0.21/0.53  % (6182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6188)Refutation not found, incomplete strategy% (6188)------------------------------
% 0.21/0.54  % (6188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6182)Memory used [KB]: 10618
% 0.21/0.54  % (6182)Time elapsed: 0.103 s
% 0.21/0.54  % (6182)------------------------------
% 0.21/0.54  % (6182)------------------------------
% 0.21/0.54  % (6188)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6188)Memory used [KB]: 10618
% 0.21/0.54  % (6188)Time elapsed: 0.102 s
% 0.21/0.54  % (6188)------------------------------
% 0.21/0.54  % (6188)------------------------------
% 0.21/0.54  % (6185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (6184)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (6205)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (6207)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (6198)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (6193)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (6186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (6192)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (6202)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (6201)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (6200)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (6195)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (6183)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (6189)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.57  % (6195)Refutation not found, incomplete strategy% (6195)------------------------------
% 0.21/0.57  % (6195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6195)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (6195)Memory used [KB]: 6396
% 0.21/0.57  % (6195)Time elapsed: 0.145 s
% 0.21/0.57  % (6195)------------------------------
% 0.21/0.57  % (6195)------------------------------
% 0.21/0.57  % (6206)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.58  % (6187)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.58  % (6194)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.58  % (6187)Refutation not found, incomplete strategy% (6187)------------------------------
% 0.21/0.58  % (6187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (6187)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (6187)Memory used [KB]: 6140
% 0.21/0.58  % (6187)Time elapsed: 0.135 s
% 0.21/0.58  % (6187)------------------------------
% 0.21/0.58  % (6187)------------------------------
% 0.21/0.58  % (6197)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.58  % (6190)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.59  % (6203)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.60  % (6191)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.61  % (6199)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.90/0.62  % (6204)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 2.09/0.64  % (6196)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 2.21/0.69  % (6190)Refutation found. Thanks to Tanya!
% 2.21/0.69  % SZS status Theorem for theBenchmark
% 2.21/0.69  % SZS output start Proof for theBenchmark
% 2.21/0.69  fof(f3574,plain,(
% 2.21/0.69    $false),
% 2.21/0.69    inference(subsumption_resolution,[],[f3436,f473])).
% 2.21/0.69  fof(f473,plain,(
% 2.21/0.69    ~v1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6))),
% 2.21/0.69    inference(backward_demodulation,[],[f459,f463])).
% 2.21/0.69  fof(f463,plain,(
% 2.21/0.69    u1_struct_0(sK8) = u1_struct_0(sK6)),
% 2.21/0.69    inference(subsumption_resolution,[],[f462,f173])).
% 2.21/0.69  fof(f173,plain,(
% 2.21/0.69    m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.21/0.69    inference(subsumption_resolution,[],[f167,f68])).
% 2.21/0.69  fof(f68,plain,(
% 2.21/0.69    l1_pre_topc(sK6)),
% 2.21/0.69    inference(cnf_transformation,[],[f45])).
% 2.21/0.69  fof(f45,plain,(
% 2.21/0.69    ((~v1_tex_2(sK8,sK6) & v1_tex_2(sK7,sK6) & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) & m1_pre_topc(sK8,sK6)) & m1_pre_topc(sK7,sK6)) & l1_pre_topc(sK6)),
% 2.21/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f19,f44,f43,f42])).
% 2.21/0.69  fof(f42,plain,(
% 2.21/0.69    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK6) & v1_tex_2(X1,sK6) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK6)) & m1_pre_topc(X1,sK6)) & l1_pre_topc(sK6))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f43,plain,(
% 2.21/0.69    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK6) & v1_tex_2(X1,sK6) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK6)) & m1_pre_topc(X1,sK6)) => (? [X2] : (~v1_tex_2(X2,sK6) & v1_tex_2(sK7,sK6) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_pre_topc(X2,sK6)) & m1_pre_topc(sK7,sK6))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f44,plain,(
% 2.21/0.69    ? [X2] : (~v1_tex_2(X2,sK6) & v1_tex_2(sK7,sK6) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_pre_topc(X2,sK6)) => (~v1_tex_2(sK8,sK6) & v1_tex_2(sK7,sK6) & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) & m1_pre_topc(sK8,sK6))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f19,plain,(
% 2.21/0.69    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f18])).
% 2.21/0.69  fof(f18,plain,(
% 2.21/0.69    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f17])).
% 2.21/0.69  fof(f17,negated_conjecture,(
% 2.21/0.69    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 2.21/0.69    inference(negated_conjecture,[],[f16])).
% 2.21/0.69  fof(f16,conjecture,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 2.21/0.69  fof(f167,plain,(
% 2.21/0.69    m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6)),
% 2.21/0.69    inference(resolution,[],[f70,f97])).
% 2.21/0.69  fof(f97,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f25])).
% 2.21/0.69  fof(f25,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f13])).
% 2.21/0.69  fof(f13,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.21/0.69  fof(f70,plain,(
% 2.21/0.69    m1_pre_topc(sK8,sK6)),
% 2.21/0.69    inference(cnf_transformation,[],[f45])).
% 2.21/0.69  fof(f462,plain,(
% 2.21/0.69    u1_struct_0(sK8) = u1_struct_0(sK6) | ~m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.21/0.69    inference(resolution,[],[f459,f109])).
% 2.21/0.69  fof(f109,plain,(
% 2.21/0.69    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.69    inference(cnf_transformation,[],[f65])).
% 2.21/0.69  fof(f65,plain,(
% 2.21/0.69    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.69    inference(nnf_transformation,[],[f31])).
% 2.21/0.69  fof(f31,plain,(
% 2.21/0.69    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f15])).
% 2.21/0.69  fof(f15,axiom,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 2.21/0.69  fof(f459,plain,(
% 2.21/0.69    ~v1_subset_1(u1_struct_0(sK8),u1_struct_0(sK6))),
% 2.21/0.69    inference(subsumption_resolution,[],[f458,f205])).
% 2.21/0.69  fof(f205,plain,(
% 2.21/0.69    ~sP4(sK6,sK8)),
% 2.21/0.69    inference(subsumption_resolution,[],[f204,f73])).
% 2.21/0.69  fof(f73,plain,(
% 2.21/0.69    ~v1_tex_2(sK8,sK6)),
% 2.21/0.69    inference(cnf_transformation,[],[f45])).
% 2.21/0.69  fof(f204,plain,(
% 2.21/0.69    v1_tex_2(sK8,sK6) | ~sP4(sK6,sK8)),
% 2.21/0.69    inference(resolution,[],[f172,f99])).
% 2.21/0.69  fof(f99,plain,(
% 2.21/0.69    ( ! [X0,X1] : (v1_tex_2(X0,X1) | ~sP4(X1,X0) | ~sP5(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f59])).
% 2.21/0.69  fof(f59,plain,(
% 2.21/0.69    ! [X0,X1] : (((v1_tex_2(X0,X1) | ~sP4(X1,X0)) & (sP4(X1,X0) | ~v1_tex_2(X0,X1))) | ~sP5(X0,X1))),
% 2.21/0.69    inference(rectify,[],[f58])).
% 2.21/0.69  fof(f58,plain,(
% 2.21/0.69    ! [X1,X0] : (((v1_tex_2(X1,X0) | ~sP4(X0,X1)) & (sP4(X0,X1) | ~v1_tex_2(X1,X0))) | ~sP5(X1,X0))),
% 2.21/0.69    inference(nnf_transformation,[],[f40])).
% 2.21/0.69  fof(f40,plain,(
% 2.21/0.69    ! [X1,X0] : ((v1_tex_2(X1,X0) <=> sP4(X0,X1)) | ~sP5(X1,X0))),
% 2.21/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.21/0.69  fof(f172,plain,(
% 2.21/0.69    sP5(sK8,sK6)),
% 2.21/0.69    inference(subsumption_resolution,[],[f166,f68])).
% 2.21/0.69  fof(f166,plain,(
% 2.21/0.69    sP5(sK8,sK6) | ~l1_pre_topc(sK6)),
% 2.21/0.69    inference(resolution,[],[f70,f104])).
% 2.21/0.69  fof(f104,plain,(
% 2.21/0.69    ( ! [X0,X1] : (sP5(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f41])).
% 2.21/0.69  fof(f41,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (sP5(X1,X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(definition_folding,[],[f27,f40,f39])).
% 2.21/0.69  fof(f39,plain,(
% 2.21/0.69    ! [X0,X1] : (sP4(X0,X1) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.21/0.69  fof(f27,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f26])).
% 2.21/0.69  fof(f26,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f14])).
% 2.21/0.69  fof(f14,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 2.21/0.69  fof(f458,plain,(
% 2.21/0.69    ~v1_subset_1(u1_struct_0(sK8),u1_struct_0(sK6)) | sP4(sK6,sK8)),
% 2.21/0.69    inference(superposition,[],[f103,f209])).
% 2.21/0.69  fof(f209,plain,(
% 2.21/0.69    u1_struct_0(sK8) = sK11(sK6,sK8)),
% 2.21/0.69    inference(resolution,[],[f205,f102])).
% 2.21/0.69  fof(f102,plain,(
% 2.21/0.69    ( ! [X0,X1] : (sP4(X0,X1) | u1_struct_0(X1) = sK11(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f63])).
% 2.21/0.69  fof(f63,plain,(
% 2.21/0.69    ! [X0,X1] : ((sP4(X0,X1) | (~v1_subset_1(sK11(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK11(X0,X1) & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X0,X1)))),
% 2.21/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f61,f62])).
% 2.21/0.69  fof(f62,plain,(
% 2.21/0.69    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK11(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK11(X0,X1) & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f61,plain,(
% 2.21/0.69    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X0,X1)))),
% 2.21/0.69    inference(rectify,[],[f60])).
% 2.21/0.69  fof(f60,plain,(
% 2.21/0.69    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X0,X1)))),
% 2.21/0.69    inference(nnf_transformation,[],[f39])).
% 2.21/0.69  fof(f103,plain,(
% 2.21/0.69    ( ! [X0,X1] : (sP4(X0,X1) | ~v1_subset_1(sK11(X0,X1),u1_struct_0(X0))) )),
% 2.21/0.69    inference(cnf_transformation,[],[f63])).
% 2.21/0.69  fof(f3436,plain,(
% 2.21/0.69    v1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6))),
% 2.21/0.69    inference(backward_demodulation,[],[f291,f3424])).
% 2.21/0.69  fof(f3424,plain,(
% 2.21/0.69    u1_struct_0(sK7) = u1_struct_0(sK6)),
% 2.21/0.69    inference(subsumption_resolution,[],[f3422,f337])).
% 2.21/0.69  fof(f337,plain,(
% 2.21/0.69    r1_tarski(u1_struct_0(sK7),u1_struct_0(sK6))),
% 2.21/0.69    inference(forward_demodulation,[],[f336,f164])).
% 2.21/0.69  fof(f164,plain,(
% 2.21/0.69    u1_struct_0(sK7) = k2_struct_0(sK7)),
% 2.21/0.69    inference(resolution,[],[f149,f77])).
% 2.21/0.69  fof(f77,plain,(
% 2.21/0.69    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f20])).
% 2.21/0.69  fof(f20,plain,(
% 2.21/0.69    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f6])).
% 2.21/0.69  fof(f6,axiom,(
% 2.21/0.69    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.21/0.69  fof(f149,plain,(
% 2.21/0.69    l1_struct_0(sK7)),
% 2.21/0.69    inference(resolution,[],[f146,f78])).
% 2.21/0.69  fof(f78,plain,(
% 2.21/0.69    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f21])).
% 2.21/0.69  fof(f21,plain,(
% 2.21/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f9])).
% 2.21/0.69  fof(f9,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.21/0.69  fof(f146,plain,(
% 2.21/0.69    l1_pre_topc(sK7)),
% 2.21/0.69    inference(subsumption_resolution,[],[f140,f68])).
% 2.21/0.69  fof(f140,plain,(
% 2.21/0.69    l1_pre_topc(sK7) | ~l1_pre_topc(sK6)),
% 2.21/0.69    inference(resolution,[],[f69,f96])).
% 2.21/0.69  fof(f96,plain,(
% 2.21/0.69    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f24])).
% 2.21/0.69  fof(f24,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f10])).
% 2.21/0.69  fof(f10,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.21/0.69  fof(f69,plain,(
% 2.21/0.69    m1_pre_topc(sK7,sK6)),
% 2.21/0.69    inference(cnf_transformation,[],[f45])).
% 2.21/0.69  fof(f336,plain,(
% 2.21/0.69    r1_tarski(k2_struct_0(sK7),u1_struct_0(sK6))),
% 2.21/0.69    inference(forward_demodulation,[],[f240,f148])).
% 2.21/0.69  fof(f148,plain,(
% 2.21/0.69    u1_struct_0(sK6) = k2_struct_0(sK6)),
% 2.21/0.69    inference(resolution,[],[f122,f77])).
% 2.21/0.69  fof(f122,plain,(
% 2.21/0.69    l1_struct_0(sK6)),
% 2.21/0.69    inference(resolution,[],[f68,f78])).
% 2.21/0.69  fof(f240,plain,(
% 2.21/0.69    r1_tarski(k2_struct_0(sK7),k2_struct_0(sK6))),
% 2.21/0.69    inference(resolution,[],[f224,f83])).
% 2.21/0.69  fof(f83,plain,(
% 2.21/0.69    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP2(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f52])).
% 2.21/0.69  fof(f52,plain,(
% 2.21/0.69    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 2.21/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f51])).
% 2.21/0.69  fof(f51,plain,(
% 2.21/0.69    ! [X1,X0] : (? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f50,plain,(
% 2.21/0.69    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 2.21/0.69    inference(rectify,[],[f49])).
% 2.21/0.69  fof(f49,plain,(
% 2.21/0.69    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 2.21/0.69    inference(flattening,[],[f48])).
% 2.21/0.69  fof(f48,plain,(
% 2.21/0.69    ! [X1,X0] : ((sP2(X1,X0) | (? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 2.21/0.69    inference(nnf_transformation,[],[f36])).
% 2.21/0.69  fof(f36,plain,(
% 2.21/0.69    ! [X1,X0] : (sP2(X1,X0) <=> (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 2.21/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.21/0.69  fof(f224,plain,(
% 2.21/0.69    sP2(sK7,sK6)),
% 2.21/0.69    inference(subsumption_resolution,[],[f222,f69])).
% 2.21/0.69  fof(f222,plain,(
% 2.21/0.69    sP2(sK7,sK6) | ~m1_pre_topc(sK7,sK6)),
% 2.21/0.69    inference(resolution,[],[f214,f81])).
% 2.21/0.69  fof(f81,plain,(
% 2.21/0.69    ( ! [X0,X1] : (sP2(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP3(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f47])).
% 2.21/0.69  fof(f47,plain,(
% 2.21/0.69    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP3(X0,X1))),
% 2.21/0.69    inference(nnf_transformation,[],[f37])).
% 2.21/0.69  fof(f37,plain,(
% 2.21/0.69    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 2.21/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.21/0.69  fof(f214,plain,(
% 2.21/0.69    sP3(sK6,sK7)),
% 2.21/0.69    inference(resolution,[],[f127,f146])).
% 2.21/0.69  fof(f127,plain,(
% 2.21/0.69    ( ! [X4] : (~l1_pre_topc(X4) | sP3(sK6,X4)) )),
% 2.21/0.69    inference(resolution,[],[f68,f95])).
% 2.21/0.69  fof(f95,plain,(
% 2.21/0.69    ( ! [X0,X1] : (sP3(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f38])).
% 2.21/0.69  fof(f38,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (sP3(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(definition_folding,[],[f23,f37,f36,f35,f34])).
% 2.21/0.69  fof(f34,plain,(
% 2.21/0.69    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.21/0.69  fof(f35,plain,(
% 2.21/0.69    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> sP0(X2,X1,X0)))),
% 2.21/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.21/0.69  fof(f23,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f7])).
% 2.21/0.69  fof(f7,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 2.21/0.69  fof(f3422,plain,(
% 2.21/0.69    u1_struct_0(sK7) = u1_struct_0(sK6) | ~r1_tarski(u1_struct_0(sK7),u1_struct_0(sK6))),
% 2.21/0.69    inference(resolution,[],[f3404,f114])).
% 2.21/0.69  fof(f114,plain,(
% 2.21/0.69    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f67])).
% 2.21/0.69  fof(f67,plain,(
% 2.21/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.69    inference(flattening,[],[f66])).
% 2.21/0.69  fof(f66,plain,(
% 2.21/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.69    inference(nnf_transformation,[],[f1])).
% 2.21/0.69  fof(f1,axiom,(
% 2.21/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.21/0.69  fof(f3404,plain,(
% 2.21/0.69    r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7))),
% 2.21/0.69    inference(backward_demodulation,[],[f2586,f3382])).
% 2.21/0.69  fof(f3382,plain,(
% 2.21/0.69    u1_struct_0(sK6) = k2_struct_0(k1_pre_topc(sK8,u1_struct_0(sK6)))),
% 2.21/0.69    inference(resolution,[],[f3328,f465])).
% 2.21/0.69  fof(f465,plain,(
% 2.21/0.69    m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.21/0.69    inference(backward_demodulation,[],[f173,f463])).
% 2.21/0.69  fof(f3328,plain,(
% 2.21/0.69    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK6))) | k2_struct_0(k1_pre_topc(sK8,X13)) = X13) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f3327,f1461])).
% 2.21/0.69  fof(f1461,plain,(
% 2.21/0.69    ( ! [X11] : (m1_pre_topc(k1_pre_topc(sK8,X11),sK8) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK6)))) )),
% 2.21/0.69    inference(forward_demodulation,[],[f189,f463])).
% 2.21/0.69  fof(f189,plain,(
% 2.21/0.69    ( ! [X11] : (m1_pre_topc(k1_pre_topc(sK8,X11),sK8) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK8)))) )),
% 2.21/0.69    inference(resolution,[],[f174,f111])).
% 2.21/0.69  fof(f111,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f33])).
% 2.21/0.69  fof(f33,plain,(
% 2.21/0.69    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f32])).
% 2.21/0.69  fof(f32,plain,(
% 2.21/0.69    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f8])).
% 2.21/0.69  fof(f8,axiom,(
% 2.21/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 2.21/0.69  fof(f174,plain,(
% 2.21/0.69    l1_pre_topc(sK8)),
% 2.21/0.69    inference(subsumption_resolution,[],[f168,f68])).
% 2.21/0.69  fof(f168,plain,(
% 2.21/0.69    l1_pre_topc(sK8) | ~l1_pre_topc(sK6)),
% 2.21/0.69    inference(resolution,[],[f70,f96])).
% 2.21/0.69  fof(f3327,plain,(
% 2.21/0.69    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK6))) | k2_struct_0(k1_pre_topc(sK8,X13)) = X13 | ~m1_pre_topc(k1_pre_topc(sK8,X13),sK8)) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f3326,f1199])).
% 2.21/0.69  fof(f1199,plain,(
% 2.21/0.69    ( ! [X10] : (v1_pre_topc(k1_pre_topc(sK8,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK6)))) )),
% 2.21/0.69    inference(forward_demodulation,[],[f188,f463])).
% 2.21/0.69  fof(f188,plain,(
% 2.21/0.69    ( ! [X10] : (v1_pre_topc(k1_pre_topc(sK8,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK8)))) )),
% 2.21/0.69    inference(resolution,[],[f174,f110])).
% 2.21/0.69  fof(f110,plain,(
% 2.21/0.69    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f33])).
% 2.21/0.69  fof(f3326,plain,(
% 2.21/0.69    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK6))) | k2_struct_0(k1_pre_topc(sK8,X13)) = X13 | ~m1_pre_topc(k1_pre_topc(sK8,X13),sK8) | ~v1_pre_topc(k1_pre_topc(sK8,X13))) )),
% 2.21/0.69    inference(forward_demodulation,[],[f191,f463])).
% 2.21/0.69  fof(f191,plain,(
% 2.21/0.69    ( ! [X13] : (k2_struct_0(k1_pre_topc(sK8,X13)) = X13 | ~m1_pre_topc(k1_pre_topc(sK8,X13),sK8) | ~v1_pre_topc(k1_pre_topc(sK8,X13)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK8)))) )),
% 2.21/0.69    inference(resolution,[],[f174,f118])).
% 2.21/0.69  fof(f118,plain,(
% 2.21/0.69    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(equality_resolution,[],[f105])).
% 2.21/0.69  fof(f105,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f64])).
% 2.21/0.69  fof(f64,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(nnf_transformation,[],[f29])).
% 2.21/0.69  fof(f29,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f28])).
% 2.21/0.69  fof(f28,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f5])).
% 2.21/0.69  fof(f5,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 2.21/0.69  fof(f2586,plain,(
% 2.21/0.69    r1_tarski(k2_struct_0(k1_pre_topc(sK8,u1_struct_0(sK6))),u1_struct_0(sK7))),
% 2.21/0.69    inference(resolution,[],[f2583,f313])).
% 2.21/0.69  fof(f313,plain,(
% 2.21/0.69    ( ! [X1] : (~sP2(X1,sK7) | r1_tarski(k2_struct_0(X1),u1_struct_0(sK7))) )),
% 2.21/0.69    inference(superposition,[],[f83,f164])).
% 2.21/0.69  fof(f2583,plain,(
% 2.21/0.69    sP2(k1_pre_topc(sK8,u1_struct_0(sK6)),sK7)),
% 2.21/0.69    inference(subsumption_resolution,[],[f2575,f1624])).
% 2.21/0.69  fof(f1624,plain,(
% 2.21/0.69    sP3(sK7,k1_pre_topc(sK8,u1_struct_0(sK6)))),
% 2.21/0.69    inference(resolution,[],[f1569,f154])).
% 2.21/0.69  fof(f154,plain,(
% 2.21/0.69    ( ! [X4] : (~l1_pre_topc(X4) | sP3(sK7,X4)) )),
% 2.21/0.69    inference(resolution,[],[f146,f95])).
% 2.21/0.69  fof(f1569,plain,(
% 2.21/0.69    l1_pre_topc(k1_pre_topc(sK8,u1_struct_0(sK6)))),
% 2.21/0.69    inference(resolution,[],[f1521,f465])).
% 2.21/0.69  fof(f1521,plain,(
% 2.21/0.69    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | l1_pre_topc(k1_pre_topc(sK8,X3))) )),
% 2.21/0.69    inference(forward_demodulation,[],[f307,f463])).
% 2.21/0.69  fof(f307,plain,(
% 2.21/0.69    ( ! [X3] : (l1_pre_topc(k1_pre_topc(sK8,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f304,f174])).
% 2.21/0.69  fof(f304,plain,(
% 2.21/0.69    ( ! [X3] : (l1_pre_topc(k1_pre_topc(sK8,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) | ~l1_pre_topc(sK8)) )),
% 2.21/0.69    inference(resolution,[],[f184,f111])).
% 2.21/0.69  fof(f184,plain,(
% 2.21/0.69    ( ! [X6] : (~m1_pre_topc(X6,sK8) | l1_pre_topc(X6)) )),
% 2.21/0.69    inference(resolution,[],[f174,f96])).
% 2.21/0.69  fof(f2575,plain,(
% 2.21/0.69    sP2(k1_pre_topc(sK8,u1_struct_0(sK6)),sK7) | ~sP3(sK7,k1_pre_topc(sK8,u1_struct_0(sK6)))),
% 2.21/0.69    inference(resolution,[],[f2532,f763])).
% 2.21/0.69  fof(f763,plain,(
% 2.21/0.69    ( ! [X5] : (~m1_pre_topc(X5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) | sP2(X5,sK7) | ~sP3(sK7,X5)) )),
% 2.21/0.69    inference(resolution,[],[f525,f81])).
% 2.21/0.69  fof(f525,plain,(
% 2.21/0.69    ( ! [X0] : (m1_pre_topc(X0,sK7) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f522,f146])).
% 2.21/0.69  fof(f522,plain,(
% 2.21/0.69    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) | m1_pre_topc(X0,sK7) | ~l1_pre_topc(sK7)) )),
% 2.21/0.69    inference(superposition,[],[f107,f464])).
% 2.21/0.69  fof(f464,plain,(
% 2.21/0.69    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))),
% 2.21/0.69    inference(backward_demodulation,[],[f71,f463])).
% 2.21/0.69  fof(f71,plain,(
% 2.21/0.69    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),
% 2.21/0.69    inference(cnf_transformation,[],[f45])).
% 2.21/0.69  fof(f107,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f30])).
% 2.21/0.69  fof(f30,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f11])).
% 2.21/0.69  fof(f11,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 2.21/0.69  fof(f2532,plain,(
% 2.21/0.69    m1_pre_topc(k1_pre_topc(sK8,u1_struct_0(sK6)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))),
% 2.21/0.69    inference(resolution,[],[f899,f465])).
% 2.21/0.69  fof(f899,plain,(
% 2.21/0.69    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) | m1_pre_topc(k1_pre_topc(sK8,X4),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))) )),
% 2.21/0.69    inference(forward_demodulation,[],[f898,f463])).
% 2.21/0.69  fof(f898,plain,(
% 2.21/0.69    ( ! [X4] : (m1_pre_topc(k1_pre_topc(sK8,X4),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK8)))) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f893,f174])).
% 2.21/0.69  fof(f893,plain,(
% 2.21/0.69    ( ! [X4] : (m1_pre_topc(k1_pre_topc(sK8,X4),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK8))) | ~l1_pre_topc(sK8)) )),
% 2.21/0.69    inference(resolution,[],[f863,f111])).
% 2.21/0.69  fof(f863,plain,(
% 2.21/0.69    ( ! [X1] : (~m1_pre_topc(X1,sK8) | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK8)))) )),
% 2.21/0.69    inference(forward_demodulation,[],[f862,f464])).
% 2.21/0.69  fof(f862,plain,(
% 2.21/0.69    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_pre_topc(X1,sK8)) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f201,f184])).
% 2.21/0.69  fof(f201,plain,(
% 2.21/0.69    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_pre_topc(X1,sK8) | ~l1_pre_topc(X1)) )),
% 2.21/0.69    inference(subsumption_resolution,[],[f198,f174])).
% 2.21/0.69  fof(f198,plain,(
% 2.21/0.69    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~m1_pre_topc(X1,sK8) | ~l1_pre_topc(sK8) | ~l1_pre_topc(X1)) )),
% 2.21/0.69    inference(superposition,[],[f79,f71])).
% 2.21/0.69  fof(f79,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f46,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(nnf_transformation,[],[f22])).
% 2.21/0.69  fof(f22,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f12])).
% 2.21/0.69  fof(f12,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 2.21/0.69  fof(f291,plain,(
% 2.21/0.69    v1_subset_1(u1_struct_0(sK7),u1_struct_0(sK6))),
% 2.21/0.69    inference(subsumption_resolution,[],[f284,f196])).
% 2.21/0.69  fof(f196,plain,(
% 2.21/0.69    sP4(sK6,sK7)),
% 2.21/0.69    inference(subsumption_resolution,[],[f194,f72])).
% 2.21/0.69  fof(f72,plain,(
% 2.21/0.69    v1_tex_2(sK7,sK6)),
% 2.21/0.69    inference(cnf_transformation,[],[f45])).
% 2.21/0.69  fof(f194,plain,(
% 2.21/0.69    sP4(sK6,sK7) | ~v1_tex_2(sK7,sK6)),
% 2.21/0.69    inference(resolution,[],[f144,f98])).
% 2.21/0.69  fof(f98,plain,(
% 2.21/0.69    ( ! [X0,X1] : (sP4(X1,X0) | ~v1_tex_2(X0,X1) | ~sP5(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f59])).
% 2.21/0.69  fof(f144,plain,(
% 2.21/0.69    sP5(sK7,sK6)),
% 2.21/0.69    inference(subsumption_resolution,[],[f138,f68])).
% 2.21/0.69  fof(f138,plain,(
% 2.21/0.69    sP5(sK7,sK6) | ~l1_pre_topc(sK6)),
% 2.21/0.69    inference(resolution,[],[f69,f104])).
% 2.21/0.69  fof(f284,plain,(
% 2.21/0.69    v1_subset_1(u1_struct_0(sK7),u1_struct_0(sK6)) | ~sP4(sK6,sK7)),
% 2.21/0.69    inference(resolution,[],[f145,f116])).
% 2.21/0.69  fof(f116,plain,(
% 2.21/0.69    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~sP4(X0,X1)) )),
% 2.21/0.69    inference(equality_resolution,[],[f100])).
% 2.21/0.69  fof(f100,plain,(
% 2.21/0.69    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP4(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f63])).
% 2.21/0.69  fof(f145,plain,(
% 2.21/0.69    m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.21/0.69    inference(subsumption_resolution,[],[f139,f68])).
% 2.21/0.69  fof(f139,plain,(
% 2.21/0.69    m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6)),
% 2.21/0.69    inference(resolution,[],[f69,f97])).
% 2.21/0.69  % SZS output end Proof for theBenchmark
% 2.21/0.69  % (6190)------------------------------
% 2.21/0.69  % (6190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.69  % (6190)Termination reason: Refutation
% 2.21/0.69  
% 2.21/0.69  % (6190)Memory used [KB]: 2814
% 2.21/0.69  % (6190)Time elapsed: 0.256 s
% 2.21/0.69  % (6190)------------------------------
% 2.21/0.69  % (6190)------------------------------
% 2.21/0.70  % (6181)Success in time 0.329 s
%------------------------------------------------------------------------------
