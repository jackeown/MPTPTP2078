%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1898+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 18.00s
% Output     : Refutation 18.00s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 143 expanded)
%              Number of leaves         :    7 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 810 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195327,plain,(
    $false ),
    inference(subsumption_resolution,[],[f195241,f8916])).

fof(f8916,plain,(
    m1_subset_1(sK70(sK69,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK69))) ),
    inference(unit_resulting_resolution,[],[f5364,f5365,f5366,f5367,f6356,f6939,f5372])).

fof(f5372,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK70(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4720])).

fof(f4720,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK70(X0,X1),X0)
            & r1_tarski(X1,sK70(X0,X1))
            & m1_subset_1(sK70(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK70])],[f3754,f4719])).

fof(f4719,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK70(X0,X1),X0)
        & r1_tarski(X1,sK70(X0,X1))
        & m1_subset_1(sK70(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3754,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3753])).

fof(f3753,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3724])).

fof(f3724,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f6939,plain,(
    v2_tex_2(k1_xboole_0,sK69) ),
    inference(unit_resulting_resolution,[],[f5364,f5365,f6358,f6356,f5367,f5596])).

fof(f5596,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3906])).

fof(f3906,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3905])).

fof(f3905,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3692])).

fof(f3692,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f6358,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f6356,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f5367,plain,(
    l1_pre_topc(sK69) ),
    inference(cnf_transformation,[],[f4718])).

fof(f4718,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK69)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK69))) )
    & l1_pre_topc(sK69)
    & v3_tdlat_3(sK69)
    & v2_pre_topc(sK69)
    & ~ v2_struct_0(sK69) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK69])],[f3748,f4717])).

fof(f4717,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK69)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK69))) )
      & l1_pre_topc(sK69)
      & v3_tdlat_3(sK69)
      & v2_pre_topc(sK69)
      & ~ v2_struct_0(sK69) ) ),
    introduced(choice_axiom,[])).

fof(f3748,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3747])).

fof(f3747,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3726])).

fof(f3726,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f3725])).

fof(f3725,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f5366,plain,(
    v3_tdlat_3(sK69) ),
    inference(cnf_transformation,[],[f4718])).

fof(f5365,plain,(
    v2_pre_topc(sK69) ),
    inference(cnf_transformation,[],[f4718])).

fof(f5364,plain,(
    ~ v2_struct_0(sK69) ),
    inference(cnf_transformation,[],[f4718])).

fof(f195241,plain,(
    ~ m1_subset_1(sK70(sK69,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK69))) ),
    inference(unit_resulting_resolution,[],[f8918,f5368])).

fof(f5368,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK69)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK69))) ) ),
    inference(cnf_transformation,[],[f4718])).

fof(f8918,plain,(
    v3_tex_2(sK70(sK69,k1_xboole_0),sK69) ),
    inference(unit_resulting_resolution,[],[f5364,f5365,f5366,f5367,f6356,f6939,f5374])).

fof(f5374,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK70(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4720])).
%------------------------------------------------------------------------------
