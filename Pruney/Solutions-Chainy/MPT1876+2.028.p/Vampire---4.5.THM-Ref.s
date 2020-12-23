%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:40 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  172 (2573 expanded)
%              Number of leaves         :   17 ( 489 expanded)
%              Depth                    :   40
%              Number of atoms          :  630 (14434 expanded)
%              Number of equality atoms :   63 ( 433 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f942,plain,(
    $false ),
    inference(subsumption_resolution,[],[f941,f839])).

fof(f839,plain,(
    l1_pre_topc(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f440,f811])).

fof(f811,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f741,f232])).

fof(f232,plain,(
    r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f231,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f231,plain,(
    r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))
    | r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f226,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f226,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_tarski(sK3(sK1)),X0),u1_struct_0(sK0))
      | r1_tarski(k1_tarski(sK3(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f223,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f223,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(sK3(sK1)),X0)
      | r2_hidden(sK4(k1_tarski(sK3(sK1)),X0),u1_struct_0(sK0))
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f217,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f217,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK1)
      | r1_tarski(k1_tarski(X2),X3)
      | r2_hidden(sK4(k1_tarski(X2),X3),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f117,f108])).

fof(f108,plain,(
    ! [X5] :
      ( r2_hidden(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X5,sK1) ) ),
    inference(resolution,[],[f76,f91])).

fof(f91,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f82,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,X6)
      | r2_hidden(sK4(k1_tarski(X4),X5),X6)
      | r1_tarski(k1_tarski(X4),X5) ) ),
    inference(resolution,[],[f107,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X4))
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X4,X3) ) ),
    inference(resolution,[],[f76,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f741,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f214,f733])).

fof(f733,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f732,f90])).

fof(f90,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(resolution,[],[f80,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f732,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tarski(sK3(sK1)))
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(resolution,[],[f726,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f726,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f725,f47])).

fof(f725,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f719])).

fof(f719,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f711,f66])).

fof(f711,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | sK1 = k1_tarski(sK3(sK1))
      | sK1 = k1_tarski(X3)
      | v1_xboole_0(k1_tarski(X3)) ) ),
    inference(resolution,[],[f705,f79])).

fof(f705,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0)
      | sK1 = k1_tarski(sK3(sK1))
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f704,f47])).

fof(f704,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK3(sK1))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f702,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f702,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f701,f441])).

fof(f441,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f440,f45])).

fof(f45,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f701,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f700,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f700,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(duplicate_literal_removal,[],[f698])).

fof(f698,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f697,f542])).

fof(f542,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(superposition,[],[f65,f537])).

fof(f537,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f536,f90])).

fof(f536,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tarski(sK3(sK1)))
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(resolution,[],[f530,f67])).

fof(f530,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | sK1 = k1_tarski(sK3(sK1))
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f526,f47])).

fof(f526,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f497,f66])).

fof(f497,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | sK1 = k1_tarski(X3)
      | v1_xboole_0(k1_tarski(X3)) ) ),
    inference(resolution,[],[f492,f79])).

fof(f492,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f491,f47])).

fof(f491,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK2(sK0,sK1))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f489,f53])).

fof(f489,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f488,f45])).

fof(f488,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f485,f47])).

fof(f485,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f482,f48])).

fof(f482,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f481,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f481,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f478,f50])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f478,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f65,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f697,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f696,f45])).

fof(f696,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f695,f433])).

fof(f433,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f430,f47])).

fof(f430,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | v2_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f428,f48])).

fof(f428,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | v2_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f427,f49])).

fof(f427,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | v2_struct_0(sK0)
      | v2_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f426,f52])).

fof(f426,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f424,f51])).

fof(f51,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f424,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_tdlat_3(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f423,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tdlat_3(X1) ) ),
    inference(subsumption_resolution,[],[f59,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f423,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f422,f49])).

fof(f422,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f421,f50])).

fof(f421,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f695,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f694,f440])).

fof(f694,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f693,f46])).

fof(f46,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f693,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f692,f49])).

fof(f692,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f691,f48])).

fof(f691,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f690,f47])).

fof(f690,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f689,f52])).

fof(f689,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f688,f50])).

fof(f688,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f373,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f373,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f372,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f57,f56])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f372,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f371,f45])).

fof(f371,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f368,f47])).

fof(f368,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f338,f48])).

fof(f338,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f337,f49])).

fof(f337,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f336,f50])).

fof(f336,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f62,f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f214,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | ~ r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f213,f132])).

fof(f132,plain,(
    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    inference(subsumption_resolution,[],[f130,f47])).

fof(f130,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f125,f66])).

fof(f125,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1) ) ),
    inference(resolution,[],[f123,f108])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(subsumption_resolution,[],[f121,f67])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f70,f67])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f213,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f212,f87])).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f211,f49])).

fof(f211,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f210,f50])).

fof(f210,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f60,f52])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f440,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f437,f47])).

fof(f437,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f429,f48])).

fof(f429,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | v1_xboole_0(X1)
      | l1_pre_topc(sK2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f425,f52])).

fof(f425,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(sK0)
      | l1_pre_topc(sK2(sK0,X1)) ) ),
    inference(resolution,[],[f423,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f941,plain,(
    ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f857,f54])).

fof(f857,plain,(
    ~ l1_struct_0(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f46,f811,f856])).

fof(f856,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(forward_demodulation,[],[f855,f733])).

fof(f855,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f854,f697])).

fof(f854,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) ),
    inference(forward_demodulation,[],[f767,f733])).

fof(f767,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v7_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))
    | ~ l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) ),
    inference(backward_demodulation,[],[f521,f733])).

fof(f521,plain,
    ( ~ v7_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))
    | ~ l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))
    | v1_zfmisc_1(k1_tarski(sK3(sK1))) ),
    inference(superposition,[],[f65,f516])).

fof(f516,plain,(
    k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) ),
    inference(resolution,[],[f515,f90])).

fof(f515,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tarski(sK3(sK1)))
      | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) ) ),
    inference(resolution,[],[f508,f67])).

fof(f508,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f507,f232])).

fof(f507,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))
    | ~ r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f505,f231])).

fof(f505,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))
    | ~ r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f486,f214])).

fof(f486,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | u1_struct_0(sK2(sK0,X0)) = X0
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f482,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.41/0.57  % (16388)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.57  % (16387)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.58  % (16404)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.58  % (16396)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.58  % (16403)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.67/0.59  % (16395)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.67/0.60  % (16403)Refutation not found, incomplete strategy% (16403)------------------------------
% 1.67/0.60  % (16403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.61  % (16403)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.61  
% 1.67/0.61  % (16403)Memory used [KB]: 10746
% 1.67/0.61  % (16403)Time elapsed: 0.155 s
% 1.67/0.61  % (16403)------------------------------
% 1.67/0.61  % (16403)------------------------------
% 1.67/0.61  % (16385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.67/0.62  % (16384)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.67/0.62  % (16386)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.67/0.62  % (16383)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.67/0.63  % (16398)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.67/0.63  % (16408)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.67/0.63  % (16392)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.67/0.63  % (16402)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.67/0.64  % (16392)Refutation not found, incomplete strategy% (16392)------------------------------
% 1.67/0.64  % (16392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.64  % (16392)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.64  
% 1.67/0.64  % (16392)Memory used [KB]: 10618
% 1.67/0.64  % (16392)Time elapsed: 0.183 s
% 1.67/0.64  % (16392)------------------------------
% 1.67/0.64  % (16392)------------------------------
% 1.67/0.64  % (16391)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.64  % (16391)Refutation not found, incomplete strategy% (16391)------------------------------
% 1.67/0.64  % (16391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.64  % (16391)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.64  
% 1.67/0.64  % (16391)Memory used [KB]: 10618
% 1.67/0.64  % (16391)Time elapsed: 0.192 s
% 1.67/0.64  % (16391)------------------------------
% 1.67/0.64  % (16391)------------------------------
% 1.67/0.64  % (16406)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.67/0.64  % (16401)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.67/0.64  % (16383)Refutation not found, incomplete strategy% (16383)------------------------------
% 1.67/0.64  % (16383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.64  % (16383)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.64  
% 1.67/0.64  % (16383)Memory used [KB]: 10746
% 1.67/0.64  % (16383)Time elapsed: 0.190 s
% 1.67/0.64  % (16383)------------------------------
% 1.67/0.64  % (16383)------------------------------
% 1.67/0.64  % (16400)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.67/0.64  % (16390)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.67/0.64  % (16399)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.67/0.65  % (16381)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.67/0.65  % (16410)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.67/0.65  % (16390)Refutation not found, incomplete strategy% (16390)------------------------------
% 1.67/0.65  % (16390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.65  % (16390)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.65  
% 1.67/0.65  % (16390)Memory used [KB]: 10746
% 1.67/0.65  % (16390)Time elapsed: 0.144 s
% 1.67/0.65  % (16390)------------------------------
% 1.67/0.65  % (16390)------------------------------
% 1.67/0.65  % (16409)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.67/0.65  % (16381)Refutation not found, incomplete strategy% (16381)------------------------------
% 1.67/0.65  % (16381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.65  % (16381)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.65  
% 1.67/0.65  % (16381)Memory used [KB]: 1663
% 1.67/0.65  % (16381)Time elapsed: 0.199 s
% 1.67/0.65  % (16381)------------------------------
% 1.67/0.65  % (16381)------------------------------
% 1.67/0.65  % (16398)Refutation not found, incomplete strategy% (16398)------------------------------
% 1.67/0.65  % (16398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.65  % (16398)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.65  
% 1.67/0.65  % (16398)Memory used [KB]: 10618
% 1.67/0.65  % (16398)Time elapsed: 0.152 s
% 1.67/0.65  % (16398)------------------------------
% 1.67/0.65  % (16398)------------------------------
% 1.67/0.65  % (16407)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.65  % (16382)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.19/0.65  % (16394)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.19/0.65  % (16393)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.19/0.65  % (16389)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.19/0.66  % (16407)Refutation not found, incomplete strategy% (16407)------------------------------
% 2.19/0.66  % (16407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (16407)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (16407)Memory used [KB]: 10746
% 2.19/0.66  % (16407)Time elapsed: 0.209 s
% 2.19/0.66  % (16407)------------------------------
% 2.19/0.66  % (16407)------------------------------
% 2.19/0.66  % (16387)Refutation found. Thanks to Tanya!
% 2.19/0.66  % SZS status Theorem for theBenchmark
% 2.19/0.66  % SZS output start Proof for theBenchmark
% 2.19/0.66  fof(f942,plain,(
% 2.19/0.66    $false),
% 2.19/0.66    inference(subsumption_resolution,[],[f941,f839])).
% 2.19/0.66  fof(f839,plain,(
% 2.19/0.66    l1_pre_topc(sK2(sK0,sK1))),
% 2.19/0.66    inference(global_subsumption,[],[f440,f811])).
% 2.26/0.66  fof(f811,plain,(
% 2.26/0.66    v2_tex_2(sK1,sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f741,f232])).
% 2.26/0.66  fof(f232,plain,(
% 2.26/0.66    r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 2.26/0.66    inference(resolution,[],[f231,f80])).
% 2.26/0.66  fof(f80,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f4])).
% 2.26/0.66  fof(f4,axiom,(
% 2.26/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.26/0.66  fof(f231,plain,(
% 2.26/0.66    r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))),
% 2.26/0.66    inference(duplicate_literal_removal,[],[f227])).
% 2.26/0.66  fof(f227,plain,(
% 2.26/0.66    r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) | r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))),
% 2.26/0.66    inference(resolution,[],[f226,f78])).
% 2.26/0.66  fof(f78,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f44])).
% 2.26/0.66  fof(f44,plain,(
% 2.26/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f2])).
% 2.26/0.66  fof(f2,axiom,(
% 2.26/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.26/0.66  fof(f226,plain,(
% 2.26/0.66    ( ! [X0] : (r2_hidden(sK4(k1_tarski(sK3(sK1)),X0),u1_struct_0(sK0)) | r1_tarski(k1_tarski(sK3(sK1)),X0)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f223,f47])).
% 2.26/0.66  fof(f47,plain,(
% 2.26/0.66    ~v1_xboole_0(sK1)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f22,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f21])).
% 2.26/0.66  fof(f21,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f19])).
% 2.26/0.66  fof(f19,negated_conjecture,(
% 2.26/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.26/0.66    inference(negated_conjecture,[],[f18])).
% 2.26/0.66  fof(f18,conjecture,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 2.26/0.66  fof(f223,plain,(
% 2.26/0.66    ( ! [X0] : (r1_tarski(k1_tarski(sK3(sK1)),X0) | r2_hidden(sK4(k1_tarski(sK3(sK1)),X0),u1_struct_0(sK0)) | v1_xboole_0(sK1)) )),
% 2.26/0.66    inference(resolution,[],[f217,f66])).
% 2.26/0.66  fof(f66,plain,(
% 2.26/0.66    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f1])).
% 2.26/0.66  fof(f1,axiom,(
% 2.26/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.26/0.66  fof(f217,plain,(
% 2.26/0.66    ( ! [X2,X3] : (~r2_hidden(X2,sK1) | r1_tarski(k1_tarski(X2),X3) | r2_hidden(sK4(k1_tarski(X2),X3),u1_struct_0(sK0))) )),
% 2.26/0.66    inference(resolution,[],[f117,f108])).
% 2.26/0.66  fof(f108,plain,(
% 2.26/0.66    ( ! [X5] : (r2_hidden(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1)) )),
% 2.26/0.66    inference(resolution,[],[f76,f91])).
% 2.26/0.66  fof(f91,plain,(
% 2.26/0.66    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.26/0.66    inference(resolution,[],[f82,f48])).
% 2.26/0.66  fof(f48,plain,(
% 2.26/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f82,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f6])).
% 2.26/0.66  fof(f6,axiom,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.26/0.66  fof(f76,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f44])).
% 2.26/0.66  fof(f117,plain,(
% 2.26/0.66    ( ! [X6,X4,X5] : (~r2_hidden(X4,X6) | r2_hidden(sK4(k1_tarski(X4),X5),X6) | r1_tarski(k1_tarski(X4),X5)) )),
% 2.26/0.66    inference(resolution,[],[f107,f77])).
% 2.26/0.66  fof(f77,plain,(
% 2.26/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f44])).
% 2.26/0.66  fof(f107,plain,(
% 2.26/0.66    ( ! [X4,X2,X3] : (~r2_hidden(X2,k1_tarski(X4)) | r2_hidden(X2,X3) | ~r2_hidden(X4,X3)) )),
% 2.26/0.66    inference(resolution,[],[f76,f79])).
% 2.26/0.66  fof(f79,plain,(
% 2.26/0.66    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f4])).
% 2.26/0.66  fof(f741,plain,(
% 2.26/0.66    v2_tex_2(sK1,sK0) | ~r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f214,f733])).
% 2.26/0.66  fof(f733,plain,(
% 2.26/0.66    sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(resolution,[],[f732,f90])).
% 2.26/0.66  fof(f90,plain,(
% 2.26/0.66    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 2.26/0.66    inference(resolution,[],[f80,f83])).
% 2.26/0.66  fof(f83,plain,(
% 2.26/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.26/0.66    inference(equality_resolution,[],[f74])).
% 2.26/0.66  fof(f74,plain,(
% 2.26/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.26/0.66    inference(cnf_transformation,[],[f3])).
% 2.26/0.66  fof(f3,axiom,(
% 2.26/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.26/0.66  fof(f732,plain,(
% 2.26/0.66    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1))) )),
% 2.26/0.66    inference(resolution,[],[f726,f67])).
% 2.26/0.66  fof(f67,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f1])).
% 2.26/0.66  fof(f726,plain,(
% 2.26/0.66    v1_xboole_0(k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f725,f47])).
% 2.26/0.66  fof(f725,plain,(
% 2.26/0.66    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1))) | v1_xboole_0(sK1)),
% 2.26/0.66    inference(duplicate_literal_removal,[],[f719])).
% 2.26/0.66  fof(f719,plain,(
% 2.26/0.66    sK1 = k1_tarski(sK3(sK1)) | sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1))) | v1_xboole_0(sK1)),
% 2.26/0.66    inference(resolution,[],[f711,f66])).
% 2.26/0.66  fof(f711,plain,(
% 2.26/0.66    ( ! [X3] : (~r2_hidden(X3,sK1) | sK1 = k1_tarski(sK3(sK1)) | sK1 = k1_tarski(X3) | v1_xboole_0(k1_tarski(X3))) )),
% 2.26/0.66    inference(resolution,[],[f705,f79])).
% 2.26/0.66  fof(f705,plain,(
% 2.26/0.66    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = k1_tarski(sK3(sK1)) | sK1 = X0) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f704,f47])).
% 2.26/0.66  fof(f704,plain,(
% 2.26/0.66    ( ! [X0] : (sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) )),
% 2.26/0.66    inference(resolution,[],[f702,f53])).
% 2.26/0.66  fof(f53,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.26/0.66    inference(cnf_transformation,[],[f24])).
% 2.26/0.66  fof(f24,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.26/0.66    inference(flattening,[],[f23])).
% 2.26/0.66  fof(f23,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f15])).
% 2.26/0.66  fof(f15,axiom,(
% 2.26/0.66    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 2.26/0.66  fof(f702,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f701,f441])).
% 2.26/0.66  fof(f441,plain,(
% 2.26/0.66    l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.26/0.66    inference(resolution,[],[f440,f45])).
% 2.26/0.66  fof(f45,plain,(
% 2.26/0.66    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f701,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1)) | ~l1_pre_topc(sK2(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f700,f54])).
% 2.26/0.66  fof(f54,plain,(
% 2.26/0.66    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f25])).
% 2.26/0.66  fof(f25,plain,(
% 2.26/0.66    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f7])).
% 2.26/0.66  fof(f7,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.26/0.66  fof(f700,plain,(
% 2.26/0.66    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(duplicate_literal_removal,[],[f698])).
% 2.26/0.66  fof(f698,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(resolution,[],[f697,f542])).
% 2.26/0.66  fof(f542,plain,(
% 2.26/0.66    ~v7_struct_0(sK2(sK0,sK1)) | ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(superposition,[],[f65,f537])).
% 2.26/0.66  fof(f537,plain,(
% 2.26/0.66    sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 2.26/0.66    inference(resolution,[],[f536,f90])).
% 2.26/0.66  fof(f536,plain,(
% 2.26/0.66    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK3(sK1))) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))) )),
% 2.26/0.66    inference(resolution,[],[f530,f67])).
% 2.26/0.66  fof(f530,plain,(
% 2.26/0.66    v1_xboole_0(k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1)) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f526,f47])).
% 2.26/0.66  fof(f526,plain,(
% 2.26/0.66    sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1))) | v1_xboole_0(sK1)),
% 2.26/0.66    inference(resolution,[],[f497,f66])).
% 2.26/0.66  fof(f497,plain,(
% 2.26/0.66    ( ! [X3] : (~r2_hidden(X3,sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(X3) | v1_xboole_0(k1_tarski(X3))) )),
% 2.26/0.66    inference(resolution,[],[f492,f79])).
% 2.26/0.66  fof(f492,plain,(
% 2.26/0.66    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = X0) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f491,f47])).
% 2.26/0.66  fof(f491,plain,(
% 2.26/0.66    ( ! [X0] : (sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) )),
% 2.26/0.66    inference(resolution,[],[f489,f53])).
% 2.26/0.66  fof(f489,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f488,f45])).
% 2.26/0.66  fof(f488,plain,(
% 2.26/0.66    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f485,f47])).
% 2.26/0.66  fof(f485,plain,(
% 2.26/0.66    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f482,f48])).
% 2.26/0.66  fof(f482,plain,(
% 2.26/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f481,f49])).
% 2.26/0.66  fof(f49,plain,(
% 2.26/0.66    ~v2_struct_0(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f481,plain,(
% 2.26/0.66    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f478,f50])).
% 2.26/0.66  fof(f50,plain,(
% 2.26/0.66    v2_pre_topc(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f478,plain,(
% 2.26/0.66    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 2.26/0.66    inference(resolution,[],[f64,f52])).
% 2.26/0.66  fof(f52,plain,(
% 2.26/0.66    l1_pre_topc(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f64,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f38,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f37])).
% 2.26/0.66  fof(f37,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f20])).
% 2.26/0.66  fof(f20,plain,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.26/0.66    inference(pure_predicate_removal,[],[f16])).
% 2.26/0.66  fof(f16,axiom,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 2.26/0.66  fof(f65,plain,(
% 2.26/0.66    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f40])).
% 2.26/0.66  fof(f40,plain,(
% 2.26/0.66    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f39])).
% 2.26/0.66  fof(f39,plain,(
% 2.26/0.66    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f9])).
% 2.26/0.66  fof(f9,axiom,(
% 2.26/0.66    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 2.26/0.66  fof(f697,plain,(
% 2.26/0.66    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.26/0.66    inference(resolution,[],[f696,f45])).
% 2.26/0.66  fof(f696,plain,(
% 2.26/0.66    ~v2_tex_2(sK1,sK0) | v7_struct_0(sK2(sK0,sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f695,f433])).
% 2.26/0.66  fof(f433,plain,(
% 2.26/0.66    ~v2_tex_2(sK1,sK0) | v2_tdlat_3(sK2(sK0,sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f430,f47])).
% 2.26/0.66  fof(f430,plain,(
% 2.26/0.66    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | v2_tdlat_3(sK2(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f428,f48])).
% 2.26/0.66  fof(f428,plain,(
% 2.26/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | v2_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f427,f49])).
% 2.26/0.66  fof(f427,plain,(
% 2.26/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | v2_struct_0(sK0) | v2_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f426,f52])).
% 2.26/0.66  fof(f426,plain,(
% 2.26/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f424,f51])).
% 2.26/0.66  fof(f51,plain,(
% 2.26/0.66    v2_tdlat_3(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f424,plain,(
% 2.26/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(resolution,[],[f423,f86])).
% 2.26/0.66  fof(f86,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tdlat_3(X1)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f59,f56])).
% 2.26/0.66  fof(f56,plain,(
% 2.26/0.66    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f29])).
% 2.26/0.66  fof(f29,plain,(
% 2.26/0.66    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f28])).
% 2.26/0.66  fof(f28,plain,(
% 2.26/0.66    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f12])).
% 2.26/0.66  fof(f12,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 2.26/0.66  fof(f59,plain,(
% 2.26/0.66    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_tdlat_3(X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f34])).
% 2.26/0.66  fof(f34,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f33])).
% 2.26/0.66  fof(f33,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f14])).
% 2.26/0.66  fof(f14,axiom,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 2.26/0.66  fof(f423,plain,(
% 2.26/0.66    ( ! [X0] : (m1_pre_topc(sK2(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f422,f49])).
% 2.26/0.66  fof(f422,plain,(
% 2.26/0.66    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f421,f50])).
% 2.26/0.66  fof(f421,plain,(
% 2.26/0.66    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 2.26/0.66    inference(resolution,[],[f63,f52])).
% 2.26/0.66  fof(f63,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f695,plain,(
% 2.26/0.66    ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f694,f440])).
% 2.26/0.66  fof(f694,plain,(
% 2.26/0.66    ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f693,f46])).
% 2.26/0.66  fof(f46,plain,(
% 2.26/0.66    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f22])).
% 2.26/0.66  fof(f693,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f692,f49])).
% 2.26/0.66  fof(f692,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f691,f48])).
% 2.26/0.66  fof(f691,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f690,f47])).
% 2.26/0.66  fof(f690,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f689,f52])).
% 2.26/0.66  fof(f689,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f688,f50])).
% 2.26/0.66  fof(f688,plain,(
% 2.26/0.66    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 2.26/0.66    inference(resolution,[],[f373,f61])).
% 2.26/0.66  fof(f61,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f373,plain,(
% 2.26/0.66    v2_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f372,f85])).
% 2.26/0.66  fof(f85,plain,(
% 2.26/0.66    ( ! [X0] : (~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f57,f56])).
% 2.26/0.66  fof(f57,plain,(
% 2.26/0.66    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f31])).
% 2.26/0.66  fof(f31,plain,(
% 2.26/0.66    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f30])).
% 2.26/0.66  fof(f30,plain,(
% 2.26/0.66    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f13])).
% 2.26/0.66  fof(f13,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 2.26/0.66  fof(f372,plain,(
% 2.26/0.66    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.26/0.66    inference(resolution,[],[f371,f45])).
% 2.26/0.66  fof(f371,plain,(
% 2.26/0.66    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f368,f47])).
% 2.26/0.66  fof(f368,plain,(
% 2.26/0.66    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f338,f48])).
% 2.26/0.66  fof(f338,plain,(
% 2.26/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f337,f49])).
% 2.26/0.66  fof(f337,plain,(
% 2.26/0.66    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f336,f50])).
% 2.26/0.66  fof(f336,plain,(
% 2.26/0.66    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 2.26/0.66    inference(resolution,[],[f62,f52])).
% 2.26/0.66  fof(f62,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1))) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f214,plain,(
% 2.26/0.66    v2_tex_2(k1_tarski(sK3(sK1)),sK0) | ~r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 2.26/0.66    inference(superposition,[],[f213,f132])).
% 2.26/0.66  fof(f132,plain,(
% 2.26/0.66    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f130,f47])).
% 2.26/0.66  fof(f130,plain,(
% 2.26/0.66    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | v1_xboole_0(sK1)),
% 2.26/0.66    inference(resolution,[],[f125,f66])).
% 2.26/0.66  fof(f125,plain,(
% 2.26/0.66    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1)) )),
% 2.26/0.66    inference(resolution,[],[f123,f108])).
% 2.26/0.66  fof(f123,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f121,f67])).
% 2.26/0.66  fof(f121,plain,(
% 2.26/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | ~r2_hidden(X1,X0)) )),
% 2.26/0.66    inference(resolution,[],[f72,f87])).
% 2.26/0.66  fof(f87,plain,(
% 2.26/0.66    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 2.26/0.66    inference(subsumption_resolution,[],[f70,f67])).
% 2.26/0.66  fof(f70,plain,(
% 2.26/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f41])).
% 2.26/0.66  fof(f41,plain,(
% 2.26/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f5])).
% 2.26/0.66  fof(f5,axiom,(
% 2.26/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.26/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.26/0.67  fof(f72,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f43])).
% 2.26/0.67  fof(f43,plain,(
% 2.26/0.67    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.26/0.67    inference(flattening,[],[f42])).
% 2.26/0.67  fof(f42,plain,(
% 2.26/0.67    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f10])).
% 2.26/0.67  fof(f10,axiom,(
% 2.26/0.67    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.26/0.67  fof(f213,plain,(
% 2.26/0.67    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 2.26/0.67    inference(resolution,[],[f212,f87])).
% 2.26/0.67  fof(f212,plain,(
% 2.26/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f211,f49])).
% 2.26/0.67  fof(f211,plain,(
% 2.26/0.67    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f210,f50])).
% 2.26/0.67  fof(f210,plain,(
% 2.26/0.67    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 2.26/0.67    inference(resolution,[],[f60,f52])).
% 2.26/0.67  fof(f60,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f36])).
% 2.26/0.67  fof(f36,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.67    inference(flattening,[],[f35])).
% 2.26/0.67  fof(f35,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.67    inference(ennf_transformation,[],[f17])).
% 2.26/0.67  fof(f17,axiom,(
% 2.26/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 2.26/0.67  fof(f440,plain,(
% 2.26/0.67    ~v2_tex_2(sK1,sK0) | l1_pre_topc(sK2(sK0,sK1))),
% 2.26/0.67    inference(subsumption_resolution,[],[f437,f47])).
% 2.26/0.67  fof(f437,plain,(
% 2.26/0.67    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | l1_pre_topc(sK2(sK0,sK1))),
% 2.26/0.67    inference(resolution,[],[f429,f48])).
% 2.26/0.67  fof(f429,plain,(
% 2.26/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v1_xboole_0(X1) | l1_pre_topc(sK2(sK0,X1))) )),
% 2.26/0.67    inference(subsumption_resolution,[],[f425,f52])).
% 2.26/0.67  fof(f425,plain,(
% 2.26/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v1_xboole_0(X1) | ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,X1))) )),
% 2.26/0.67    inference(resolution,[],[f423,f58])).
% 2.26/0.67  fof(f58,plain,(
% 2.26/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f32])).
% 2.26/0.67  fof(f32,plain,(
% 2.26/0.67    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.67    inference(ennf_transformation,[],[f8])).
% 2.26/0.67  fof(f8,axiom,(
% 2.26/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.26/0.67  fof(f941,plain,(
% 2.26/0.67    ~l1_pre_topc(sK2(sK0,sK1))),
% 2.26/0.67    inference(resolution,[],[f857,f54])).
% 2.26/0.67  fof(f857,plain,(
% 2.26/0.67    ~l1_struct_0(sK2(sK0,sK1))),
% 2.26/0.67    inference(global_subsumption,[],[f46,f811,f856])).
% 2.26/0.67  fof(f856,plain,(
% 2.26/0.67    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.26/0.67    inference(forward_demodulation,[],[f855,f733])).
% 2.26/0.67  fof(f855,plain,(
% 2.26/0.67    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))),
% 2.26/0.67    inference(subsumption_resolution,[],[f854,f697])).
% 2.26/0.67  fof(f854,plain,(
% 2.26/0.67    ~v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))),
% 2.26/0.67    inference(forward_demodulation,[],[f767,f733])).
% 2.26/0.67  fof(f767,plain,(
% 2.26/0.67    v1_zfmisc_1(sK1) | ~v7_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) | ~l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))),
% 2.26/0.67    inference(backward_demodulation,[],[f521,f733])).
% 2.26/0.67  fof(f521,plain,(
% 2.26/0.67    ~v7_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) | ~l1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) | v1_zfmisc_1(k1_tarski(sK3(sK1)))),
% 2.26/0.67    inference(superposition,[],[f65,f516])).
% 2.26/0.67  fof(f516,plain,(
% 2.26/0.67    k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))),
% 2.26/0.67    inference(resolution,[],[f515,f90])).
% 2.26/0.67  fof(f515,plain,(
% 2.26/0.67    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK3(sK1))) | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))) )),
% 2.26/0.67    inference(resolution,[],[f508,f67])).
% 2.26/0.67  fof(f508,plain,(
% 2.26/0.67    v1_xboole_0(k1_tarski(sK3(sK1))) | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1))))),
% 2.26/0.67    inference(subsumption_resolution,[],[f507,f232])).
% 2.26/0.67  fof(f507,plain,(
% 2.26/0.67    v1_xboole_0(k1_tarski(sK3(sK1))) | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) | ~r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 2.26/0.67    inference(subsumption_resolution,[],[f505,f231])).
% 2.26/0.67  fof(f505,plain,(
% 2.26/0.67    v1_xboole_0(k1_tarski(sK3(sK1))) | k1_tarski(sK3(sK1)) = u1_struct_0(sK2(sK0,k1_tarski(sK3(sK1)))) | ~r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 2.26/0.67    inference(resolution,[],[f486,f214])).
% 2.26/0.67  fof(f486,plain,(
% 2.26/0.67    ( ! [X0] : (~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0 | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 2.26/0.67    inference(resolution,[],[f482,f81])).
% 2.26/0.67  fof(f81,plain,(
% 2.26/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.26/0.67    inference(cnf_transformation,[],[f6])).
% 2.26/0.67  % SZS output end Proof for theBenchmark
% 2.26/0.67  % (16387)------------------------------
% 2.26/0.67  % (16387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.67  % (16387)Termination reason: Refutation
% 2.26/0.67  
% 2.26/0.67  % (16387)Memory used [KB]: 7291
% 2.26/0.67  % (16387)Time elapsed: 0.211 s
% 2.26/0.67  % (16387)------------------------------
% 2.26/0.67  % (16387)------------------------------
% 2.26/0.67  % (16397)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.26/0.67  % (16380)Success in time 0.293 s
%------------------------------------------------------------------------------
