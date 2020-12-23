%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:34 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  136 (1068 expanded)
%              Number of leaves         :   22 ( 364 expanded)
%              Depth                    :   31
%              Number of atoms          :  471 (6041 expanded)
%              Number of equality atoms :   72 (1057 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f751,plain,(
    $false ),
    inference(subsumption_resolution,[],[f692,f95])).

fof(f95,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(superposition,[],[f63,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f692,plain,(
    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f152,f668])).

fof(f668,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f667,f97])).

fof(f97,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f96,f58])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f46,f45,f44])).

fof(f44,plain,
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
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f667,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f662,f190])).

fof(f190,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f188,f97])).

fof(f188,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f183,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f183,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f182,f98])).

fof(f98,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f96,f59])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f182,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f167,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f167,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | m1_pre_topc(X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    inference(forward_demodulation,[],[f166,f60])).

fof(f60,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f166,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | m1_pre_topc(X5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(resolution,[],[f161,f98])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(subsumption_resolution,[],[f67,f69])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f662,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f652])).

fof(f652,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(resolution,[],[f648,f541])).

fof(f541,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f532,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f532,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK2,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f437,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f437,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK2,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f435,f234])).

fof(f234,plain,(
    ! [X1] :
      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f70,f224])).

fof(f224,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK0) ),
    inference(superposition,[],[f223,f208])).

fof(f208,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f207,f57])).

fof(f207,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f204,f59])).

fof(f204,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f75,f62])).

fof(f62,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f223,plain,(
    u1_struct_0(sK0) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f222,f57])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f219,f59])).

fof(f219,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK3(sK0,sK2) ),
    inference(resolution,[],[f218,f62])).

fof(f218,plain,(
    ! [X6,X5] :
      ( v1_tex_2(X5,X6)
      | ~ m1_pre_topc(X5,X6)
      | ~ l1_pre_topc(X6)
      | u1_struct_0(X6) = sK3(X6,X5) ) ),
    inference(subsumption_resolution,[],[f215,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f215,plain,(
    ! [X6,X5] :
      ( v1_tex_2(X5,X6)
      | ~ m1_pre_topc(X5,X6)
      | ~ l1_pre_topc(X6)
      | u1_struct_0(X6) = sK3(X6,X5)
      | v1_subset_1(sK3(X6,X5),u1_struct_0(X6)) ) ),
    inference(resolution,[],[f74,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (14730)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f435,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK2,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f393,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f393,plain,(
    ! [X0] :
      ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK2,X0) ) ),
    inference(superposition,[],[f107,f224])).

fof(f107,plain,(
    ! [X4,X3] :
      ( v1_subset_1(u1_struct_0(X3),u1_struct_0(X4))
      | ~ l1_pre_topc(X4)
      | u1_struct_0(X4) = u1_struct_0(X3)
      | ~ m1_pre_topc(X3,X4) ) ),
    inference(resolution,[],[f70,f89])).

fof(f648,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f647,f97])).

fof(f647,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f645,f190])).

fof(f645,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f642,f234])).

fof(f642,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f640])).

fof(f640,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f636,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f636,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1),u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK1) = u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f635,f97])).

fof(f635,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK4(u1_struct_0(sK1),u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f629,f190])).

fof(f629,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK4(u1_struct_0(sK1),u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f609,f281])).

fof(f281,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f276,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f276,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f269,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f269,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f247,f174])).

fof(f174,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(resolution,[],[f172,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f142,f98])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f77,f60])).

fof(f172,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f171,f97])).

fof(f171,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f165,f66])).

fof(f165,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK1)
      | m1_pre_topc(X4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    inference(resolution,[],[f161,f97])).

fof(f247,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f233,f98])).

fof(f233,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f70,f224])).

fof(f609,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(u1_struct_0(X0),u1_struct_0(sK0)),u1_struct_0(X0))
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f145,f224])).

fof(f145,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(u1_struct_0(X0),u1_struct_0(X1)),u1_struct_0(X0))
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f86,f70])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f152,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f151,f57])).

fof(f151,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f150,f58])).

fof(f150,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

% (14738)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f70,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (14735)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (14727)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14722)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14719)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (14718)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.27/0.52  % (14715)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.52  % (14724)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.27/0.53  % (14723)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.27/0.53  % (14714)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.27/0.54  % (14717)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.27/0.54  % (14716)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.27/0.54  % (14735)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % (14725)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.40/0.54  % (14714)Refutation not found, incomplete strategy% (14714)------------------------------
% 1.40/0.54  % (14714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14726)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.40/0.54  % (14736)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.40/0.55  % (14728)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.40/0.55  % (14729)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.40/0.55  % (14720)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.40/0.55  % (14739)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.40/0.55  % (14734)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.40/0.55  % (14733)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f751,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(subsumption_resolution,[],[f692,f95])).
% 1.40/0.55  fof(f95,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.40/0.55    inference(superposition,[],[f63,f64])).
% 1.40/0.55  fof(f64,plain,(
% 1.40/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.40/0.55  fof(f692,plain,(
% 1.40/0.55    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.40/0.55    inference(superposition,[],[f152,f668])).
% 1.40/0.55  fof(f668,plain,(
% 1.40/0.55    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f667,f97])).
% 1.40/0.55  fof(f97,plain,(
% 1.40/0.55    l1_pre_topc(sK1)),
% 1.40/0.55    inference(resolution,[],[f96,f58])).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    m1_pre_topc(sK1,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f46,f45,f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.40/0.55    inference(flattening,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,negated_conjecture,(
% 1.40/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 1.40/0.55    inference(negated_conjecture,[],[f20])).
% 1.40/0.55  fof(f20,conjecture,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).
% 1.40/0.55  fof(f96,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.40/0.55    inference(resolution,[],[f69,f57])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    l1_pre_topc(sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f69,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.40/0.55  fof(f667,plain,(
% 1.40/0.55    u1_struct_0(sK1) = u1_struct_0(sK0) | ~l1_pre_topc(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f662,f190])).
% 1.40/0.55  fof(f190,plain,(
% 1.40/0.55    m1_pre_topc(sK2,sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f188,f97])).
% 1.40/0.55  fof(f188,plain,(
% 1.40/0.55    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 1.40/0.55    inference(resolution,[],[f183,f77])).
% 1.40/0.55  fof(f77,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.40/0.55  fof(f183,plain,(
% 1.40/0.55    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.40/0.55    inference(subsumption_resolution,[],[f182,f98])).
% 1.40/0.55  fof(f98,plain,(
% 1.40/0.55    l1_pre_topc(sK2)),
% 1.40/0.55    inference(resolution,[],[f96,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    m1_pre_topc(sK2,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f182,plain,(
% 1.40/0.55    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2)),
% 1.40/0.55    inference(resolution,[],[f167,f66])).
% 1.40/0.55  fof(f66,plain,(
% 1.40/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f16])).
% 1.40/0.55  fof(f16,axiom,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.40/0.55  fof(f167,plain,(
% 1.40/0.55    ( ! [X5] : (~m1_pre_topc(X5,sK2) | m1_pre_topc(X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )),
% 1.40/0.55    inference(forward_demodulation,[],[f166,f60])).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f166,plain,(
% 1.40/0.55    ( ! [X5] : (~m1_pre_topc(X5,sK2) | m1_pre_topc(X5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) )),
% 1.40/0.55    inference(resolution,[],[f161,f98])).
% 1.40/0.55  fof(f161,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f67,f69])).
% 1.40/0.55  fof(f67,plain,(
% 1.40/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(nnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.40/0.55  fof(f662,plain,(
% 1.40/0.55    u1_struct_0(sK1) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f652])).
% 1.40/0.55  fof(f652,plain,(
% 1.40/0.55    u1_struct_0(sK1) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.40/0.55    inference(resolution,[],[f648,f541])).
% 1.40/0.55  fof(f541,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(sK0)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f532,f91])).
% 1.40/0.55  fof(f91,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.40/0.55  fof(f532,plain,(
% 1.40/0.55    ( ! [X0] : (u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,X0) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 1.40/0.55    inference(resolution,[],[f437,f78])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.40/0.55  fof(f437,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,X0) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f435,f234])).
% 1.40/0.55  fof(f234,plain,(
% 1.40/0.55    ( ! [X1] : (m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1)) )),
% 1.40/0.55    inference(superposition,[],[f70,f224])).
% 1.40/0.55  fof(f224,plain,(
% 1.40/0.55    u1_struct_0(sK2) = u1_struct_0(sK0)),
% 1.40/0.55    inference(superposition,[],[f223,f208])).
% 1.40/0.55  fof(f208,plain,(
% 1.40/0.55    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f207,f57])).
% 1.40/0.55  fof(f207,plain,(
% 1.40/0.55    u1_struct_0(sK2) = sK3(sK0,sK2) | ~l1_pre_topc(sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f204,f59])).
% 1.40/0.55  fof(f204,plain,(
% 1.40/0.55    u1_struct_0(sK2) = sK3(sK0,sK2) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 1.40/0.55    inference(resolution,[],[f75,f62])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ~v1_tex_2(sK2,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f75,plain,(
% 1.40/0.55    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(rectify,[],[f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(nnf_transformation,[],[f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(flattening,[],[f30])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,axiom,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 1.40/0.55  fof(f223,plain,(
% 1.40/0.55    u1_struct_0(sK0) = sK3(sK0,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f222,f57])).
% 1.40/0.55  fof(f222,plain,(
% 1.40/0.55    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK3(sK0,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f219,f59])).
% 1.40/0.55  fof(f219,plain,(
% 1.40/0.55    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK3(sK0,sK2)),
% 1.40/0.55    inference(resolution,[],[f218,f62])).
% 1.40/0.55  fof(f218,plain,(
% 1.40/0.55    ( ! [X6,X5] : (v1_tex_2(X5,X6) | ~m1_pre_topc(X5,X6) | ~l1_pre_topc(X6) | u1_struct_0(X6) = sK3(X6,X5)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f215,f76])).
% 1.40/0.55  fof(f76,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f52])).
% 1.40/0.55  fof(f215,plain,(
% 1.40/0.55    ( ! [X6,X5] : (v1_tex_2(X5,X6) | ~m1_pre_topc(X5,X6) | ~l1_pre_topc(X6) | u1_struct_0(X6) = sK3(X6,X5) | v1_subset_1(sK3(X6,X5),u1_struct_0(X6))) )),
% 1.40/0.55    inference(resolution,[],[f74,f89])).
% 1.40/0.55  fof(f89,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f56])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.55    inference(nnf_transformation,[],[f41])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,axiom,(
% 1.40/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.40/0.55  fof(f74,plain,(
% 1.40/0.55    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f52])).
% 1.40/0.55  fof(f70,plain,(
% 1.40/0.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f28])).
% 1.40/0.55  % (14730)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.40/0.55  fof(f435,plain,(
% 1.40/0.55    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,X0) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(u1_struct_0(X0))) )),
% 1.40/0.55    inference(resolution,[],[f393,f149])).
% 1.40/0.55  fof(f149,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f81,f79])).
% 1.40/0.55  fof(f79,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.40/0.55  fof(f81,plain,(
% 1.40/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.40/0.55    inference(flattening,[],[f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,axiom,(
% 1.40/0.55    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).
% 1.40/0.55  fof(f393,plain,(
% 1.40/0.55    ( ! [X0] : (v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,X0)) )),
% 1.40/0.55    inference(superposition,[],[f107,f224])).
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    ( ! [X4,X3] : (v1_subset_1(u1_struct_0(X3),u1_struct_0(X4)) | ~l1_pre_topc(X4) | u1_struct_0(X4) = u1_struct_0(X3) | ~m1_pre_topc(X3,X4)) )),
% 1.40/0.55    inference(resolution,[],[f70,f89])).
% 1.40/0.55  fof(f648,plain,(
% 1.40/0.55    v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f647,f97])).
% 1.40/0.55  fof(f647,plain,(
% 1.40/0.55    v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0) | ~l1_pre_topc(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f645,f190])).
% 1.40/0.55  fof(f645,plain,(
% 1.40/0.55    v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 1.40/0.55    inference(resolution,[],[f642,f234])).
% 1.40/0.55  fof(f642,plain,(
% 1.40/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f640])).
% 1.40/0.55  fof(f640,plain,(
% 1.40/0.55    u1_struct_0(sK1) = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.40/0.55    inference(resolution,[],[f636,f87])).
% 1.40/0.55  fof(f87,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f40,plain,(
% 1.40/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(flattening,[],[f39])).
% 1.40/0.56  fof(f39,plain,(
% 1.40/0.56    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 1.40/0.56  fof(f636,plain,(
% 1.40/0.56    r2_hidden(sK4(u1_struct_0(sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK1) = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK1))),
% 1.40/0.56    inference(subsumption_resolution,[],[f635,f97])).
% 1.40/0.56  fof(f635,plain,(
% 1.40/0.56    u1_struct_0(sK1) = u1_struct_0(sK0) | ~l1_pre_topc(sK1) | r2_hidden(sK4(u1_struct_0(sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.40/0.56    inference(subsumption_resolution,[],[f629,f190])).
% 1.40/0.56  fof(f629,plain,(
% 1.40/0.56    u1_struct_0(sK1) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | r2_hidden(sK4(u1_struct_0(sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.40/0.56    inference(resolution,[],[f609,f281])).
% 1.40/0.56  fof(f281,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 1.40/0.56    inference(resolution,[],[f276,f82])).
% 1.40/0.56  fof(f82,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f53])).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.40/0.56    inference(nnf_transformation,[],[f38])).
% 1.40/0.56  fof(f38,plain,(
% 1.40/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.40/0.56  fof(f276,plain,(
% 1.40/0.56    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | r2_hidden(X0,u1_struct_0(sK0))) )),
% 1.40/0.56    inference(resolution,[],[f269,f90])).
% 1.40/0.56  fof(f90,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f42])).
% 1.40/0.56  fof(f42,plain,(
% 1.40/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.40/0.56  fof(f269,plain,(
% 1.40/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.56    inference(resolution,[],[f247,f174])).
% 1.40/0.56  fof(f174,plain,(
% 1.40/0.56    m1_pre_topc(sK1,sK2)),
% 1.40/0.56    inference(resolution,[],[f172,f143])).
% 1.40/0.56  fof(f143,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK2)) )),
% 1.40/0.56    inference(subsumption_resolution,[],[f142,f98])).
% 1.40/0.56  fof(f142,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 1.40/0.56    inference(superposition,[],[f77,f60])).
% 1.40/0.56  fof(f172,plain,(
% 1.40/0.56    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.40/0.56    inference(subsumption_resolution,[],[f171,f97])).
% 1.40/0.56  fof(f171,plain,(
% 1.40/0.56    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 1.40/0.56    inference(resolution,[],[f165,f66])).
% 1.40/0.56  fof(f165,plain,(
% 1.40/0.56    ( ! [X4] : (~m1_pre_topc(X4,sK1) | m1_pre_topc(X4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )),
% 1.40/0.56    inference(resolution,[],[f161,f97])).
% 1.40/0.56  fof(f247,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.40/0.56    inference(subsumption_resolution,[],[f233,f98])).
% 1.40/0.56  fof(f233,plain,(
% 1.40/0.56    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 1.40/0.56    inference(superposition,[],[f70,f224])).
% 1.40/0.56  fof(f609,plain,(
% 1.40/0.56    ( ! [X0] : (m1_subset_1(sK4(u1_struct_0(X0),u1_struct_0(sK0)),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.56    inference(superposition,[],[f145,f224])).
% 1.40/0.56  fof(f145,plain,(
% 1.40/0.56    ( ! [X0,X1] : (m1_subset_1(sK4(u1_struct_0(X0),u1_struct_0(X1)),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.56    inference(resolution,[],[f86,f70])).
% 1.40/0.56  fof(f86,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1),X0) | X0 = X1) )),
% 1.40/0.56    inference(cnf_transformation,[],[f55])).
% 1.40/0.56  fof(f152,plain,(
% 1.40/0.56    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.40/0.56    inference(subsumption_resolution,[],[f151,f57])).
% 1.40/0.56  fof(f151,plain,(
% 1.40/0.56    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.40/0.56    inference(subsumption_resolution,[],[f150,f58])).
% 1.40/0.56  fof(f150,plain,(
% 1.40/0.56    ~m1_pre_topc(sK1,sK0) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.40/0.56    inference(resolution,[],[f94,f61])).
% 1.40/0.56  fof(f61,plain,(
% 1.40/0.56    v1_tex_2(sK1,sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f47])).
% 1.40/0.56  % (14738)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.40/0.56    inference(global_subsumption,[],[f70,f92])).
% 1.40/0.56  fof(f92,plain,(
% 1.40/0.56    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.56    inference(equality_resolution,[],[f73])).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f52])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (14735)------------------------------
% 1.40/0.56  % (14735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (14735)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (14735)Memory used [KB]: 6652
% 1.40/0.56  % (14735)Time elapsed: 0.115 s
% 1.40/0.56  % (14735)------------------------------
% 1.40/0.56  % (14735)------------------------------
% 1.40/0.56  % (14721)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.40/0.56  % (14731)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.40/0.56  % (14714)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (14714)Memory used [KB]: 10746
% 1.40/0.56  % (14714)Time elapsed: 0.123 s
% 1.40/0.56  % (14713)Success in time 0.202 s
%------------------------------------------------------------------------------
