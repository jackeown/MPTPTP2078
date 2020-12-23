%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1848+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 116 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 444 expanded)
%              Number of equality atoms :   19 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5599,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5595,f5497])).

fof(f5497,plain,(
    v1_subset_1(u1_struct_0(sK23),u1_struct_0(sK23)) ),
    inference(subsumption_resolution,[],[f5496,f5357])).

fof(f5357,plain,(
    m1_subset_1(u1_struct_0(sK23),k1_zfmisc_1(u1_struct_0(sK23))) ),
    inference(forward_demodulation,[],[f5356,f4327])).

fof(f4327,plain,(
    u1_struct_0(sK23) = u1_struct_0(sK24) ),
    inference(cnf_transformation,[],[f4022])).

fof(f4022,plain,
    ( v1_tex_2(sK24,sK23)
    & u1_struct_0(sK23) = u1_struct_0(sK24)
    & m1_pre_topc(sK24,sK23)
    & l1_pre_topc(sK23) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24])],[f3613,f4021,f4020])).

fof(f4020,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_tex_2(X1,X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( v1_tex_2(X1,sK23)
          & u1_struct_0(X1) = u1_struct_0(sK23)
          & m1_pre_topc(X1,sK23) )
      & l1_pre_topc(sK23) ) ),
    introduced(choice_axiom,[])).

fof(f4021,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK23)
        & u1_struct_0(X1) = u1_struct_0(sK23)
        & m1_pre_topc(X1,sK23) )
   => ( v1_tex_2(sK24,sK23)
      & u1_struct_0(sK23) = u1_struct_0(sK24)
      & m1_pre_topc(sK24,sK23) ) ),
    introduced(choice_axiom,[])).

fof(f3613,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3612])).

fof(f3612,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3598])).

fof(f3598,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3597])).

fof(f3597,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(f5356,plain,(
    m1_subset_1(u1_struct_0(sK24),k1_zfmisc_1(u1_struct_0(sK23))) ),
    inference(subsumption_resolution,[],[f5228,f4325])).

fof(f4325,plain,(
    l1_pre_topc(sK23) ),
    inference(cnf_transformation,[],[f4022])).

fof(f5228,plain,
    ( m1_subset_1(u1_struct_0(sK24),k1_zfmisc_1(u1_struct_0(sK23)))
    | ~ l1_pre_topc(sK23) ),
    inference(resolution,[],[f4326,f4346])).

fof(f4346,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3633])).

fof(f3633,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3441])).

fof(f3441,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f4326,plain,(
    m1_pre_topc(sK24,sK23) ),
    inference(cnf_transformation,[],[f4022])).

fof(f5496,plain,
    ( ~ m1_subset_1(u1_struct_0(sK23),k1_zfmisc_1(u1_struct_0(sK23)))
    | v1_subset_1(u1_struct_0(sK23),u1_struct_0(sK23)) ),
    inference(forward_demodulation,[],[f5495,f4327])).

fof(f5495,plain,
    ( v1_subset_1(u1_struct_0(sK23),u1_struct_0(sK23))
    | ~ m1_subset_1(u1_struct_0(sK24),k1_zfmisc_1(u1_struct_0(sK23))) ),
    inference(forward_demodulation,[],[f5494,f4327])).

fof(f5494,plain,
    ( v1_subset_1(u1_struct_0(sK24),u1_struct_0(sK23))
    | ~ m1_subset_1(u1_struct_0(sK24),k1_zfmisc_1(u1_struct_0(sK23))) ),
    inference(subsumption_resolution,[],[f5493,f4325])).

fof(f5493,plain,
    ( v1_subset_1(u1_struct_0(sK24),u1_struct_0(sK23))
    | ~ m1_subset_1(u1_struct_0(sK24),k1_zfmisc_1(u1_struct_0(sK23)))
    | ~ l1_pre_topc(sK23) ),
    inference(subsumption_resolution,[],[f5311,f4328])).

fof(f4328,plain,(
    v1_tex_2(sK24,sK23) ),
    inference(cnf_transformation,[],[f4022])).

fof(f5311,plain,
    ( v1_subset_1(u1_struct_0(sK24),u1_struct_0(sK23))
    | ~ v1_tex_2(sK24,sK23)
    | ~ m1_subset_1(u1_struct_0(sK24),k1_zfmisc_1(u1_struct_0(sK23)))
    | ~ l1_pre_topc(sK23) ),
    inference(resolution,[],[f4326,f4905])).

fof(f4905,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f4330])).

fof(f4330,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4023])).

fof(f4023,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3615])).

fof(f3615,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3614])).

fof(f3614,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3595])).

fof(f3595,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

fof(f5595,plain,(
    ~ v1_subset_1(u1_struct_0(sK23),u1_struct_0(sK23)) ),
    inference(backward_demodulation,[],[f5566,f5584])).

fof(f5584,plain,(
    u1_struct_0(sK23) = k2_struct_0(sK23) ),
    inference(resolution,[],[f5033,f4652])).

fof(f4652,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3827])).

fof(f3827,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f5033,plain,(
    l1_struct_0(sK23) ),
    inference(resolution,[],[f4325,f4580])).

fof(f4580,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3791])).

fof(f3791,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f5566,plain,(
    ~ v1_subset_1(k2_struct_0(sK23),u1_struct_0(sK23)) ),
    inference(resolution,[],[f5033,f4396])).

fof(f4396,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3674])).

fof(f3674,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1791])).

fof(f1791,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
%------------------------------------------------------------------------------
