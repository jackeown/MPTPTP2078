%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1277+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 6.58s
% Output     : Refutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 146 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 651 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9037,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9036,f3009])).

fof(f3009,plain,(
    ~ v3_tops_1(k2_tops_1(sK29,sK30),sK29) ),
    inference(cnf_transformation,[],[f2731])).

fof(f2731,plain,
    ( ~ v3_tops_1(k2_tops_1(sK29,sK30),sK29)
    & v4_pre_topc(sK30,sK29)
    & m1_subset_1(sK30,k1_zfmisc_1(u1_struct_0(sK29)))
    & l1_pre_topc(sK29)
    & v2_pre_topc(sK29) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29,sK30])],[f2197,f2730,f2729])).

fof(f2729,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(sK29,X1),sK29)
          & v4_pre_topc(X1,sK29)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK29))) )
      & l1_pre_topc(sK29)
      & v2_pre_topc(sK29) ) ),
    introduced(choice_axiom,[])).

fof(f2730,plain,
    ( ? [X1] :
        ( ~ v3_tops_1(k2_tops_1(sK29,X1),sK29)
        & v4_pre_topc(X1,sK29)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK29))) )
   => ( ~ v3_tops_1(k2_tops_1(sK29,sK30),sK29)
      & v4_pre_topc(sK30,sK29)
      & m1_subset_1(sK30,k1_zfmisc_1(u1_struct_0(sK29))) ) ),
    introduced(choice_axiom,[])).

fof(f2197,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2196])).

fof(f2196,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2187])).

fof(f2187,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2186])).

fof(f2186,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).

fof(f9036,plain,(
    v3_tops_1(k2_tops_1(sK29,sK30),sK29) ),
    inference(forward_demodulation,[],[f9035,f4562])).

fof(f4562,plain,(
    k2_tops_1(sK29,sK30) = k2_tops_1(sK29,k4_xboole_0(u1_struct_0(sK29),sK30)) ),
    inference(backward_demodulation,[],[f4408,f4329])).

fof(f4329,plain,(
    k3_subset_1(u1_struct_0(sK29),sK30) = k4_xboole_0(u1_struct_0(sK29),sK30) ),
    inference(resolution,[],[f3007,f3245])).

fof(f3245,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2374])).

fof(f2374,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3007,plain,(
    m1_subset_1(sK30,k1_zfmisc_1(u1_struct_0(sK29))) ),
    inference(cnf_transformation,[],[f2731])).

fof(f4408,plain,(
    k2_tops_1(sK29,sK30) = k2_tops_1(sK29,k3_subset_1(u1_struct_0(sK29),sK30)) ),
    inference(subsumption_resolution,[],[f4148,f3006])).

fof(f3006,plain,(
    l1_pre_topc(sK29) ),
    inference(cnf_transformation,[],[f2731])).

fof(f4148,plain,
    ( k2_tops_1(sK29,sK30) = k2_tops_1(sK29,k3_subset_1(u1_struct_0(sK29),sK30))
    | ~ l1_pre_topc(sK29) ),
    inference(resolution,[],[f3007,f3039])).

fof(f3039,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2232])).

fof(f2232,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2156])).

fof(f2156,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f9035,plain,(
    v3_tops_1(k2_tops_1(sK29,k4_xboole_0(u1_struct_0(sK29),sK30)),sK29) ),
    inference(subsumption_resolution,[],[f9034,f3005])).

fof(f3005,plain,(
    v2_pre_topc(sK29) ),
    inference(cnf_transformation,[],[f2731])).

fof(f9034,plain,
    ( v3_tops_1(k2_tops_1(sK29,k4_xboole_0(u1_struct_0(sK29),sK30)),sK29)
    | ~ v2_pre_topc(sK29) ),
    inference(subsumption_resolution,[],[f9033,f3006])).

fof(f9033,plain,
    ( v3_tops_1(k2_tops_1(sK29,k4_xboole_0(u1_struct_0(sK29),sK30)),sK29)
    | ~ l1_pre_topc(sK29)
    | ~ v2_pre_topc(sK29) ),
    inference(subsumption_resolution,[],[f9001,f4568])).

fof(f4568,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK29),sK30),k1_zfmisc_1(u1_struct_0(sK29))) ),
    inference(forward_demodulation,[],[f4330,f4329])).

fof(f4330,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK29),sK30),k1_zfmisc_1(u1_struct_0(sK29))) ),
    inference(resolution,[],[f3007,f3246])).

fof(f3246,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2375])).

fof(f2375,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f9001,plain,
    ( v3_tops_1(k2_tops_1(sK29,k4_xboole_0(u1_struct_0(sK29),sK30)),sK29)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK29),sK30),k1_zfmisc_1(u1_struct_0(sK29)))
    | ~ l1_pre_topc(sK29)
    | ~ v2_pre_topc(sK29) ),
    inference(resolution,[],[f4533,f3010])).

fof(f3010,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2199])).

fof(f2199,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2198])).

fof(f2198,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2105])).

fof(f2105,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_tops_1(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_tops_1)).

fof(f4533,plain,(
    v3_pre_topc(k4_xboole_0(u1_struct_0(sK29),sK30),sK29) ),
    inference(backward_demodulation,[],[f4089,f4329])).

fof(f4089,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK29),sK30),sK29) ),
    inference(subsumption_resolution,[],[f4088,f3005])).

fof(f4088,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK29),sK30),sK29)
    | ~ v2_pre_topc(sK29) ),
    inference(subsumption_resolution,[],[f4087,f3006])).

fof(f4087,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK29),sK30),sK29)
    | ~ l1_pre_topc(sK29)
    | ~ v2_pre_topc(sK29) ),
    inference(subsumption_resolution,[],[f4056,f3007])).

fof(f4056,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK29),sK30),sK29)
    | ~ m1_subset_1(sK30,k1_zfmisc_1(u1_struct_0(sK29)))
    | ~ l1_pre_topc(sK29)
    | ~ v2_pre_topc(sK29) ),
    inference(resolution,[],[f3008,f3053])).

fof(f3053,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2242])).

fof(f2242,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2241])).

fof(f2241,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2107])).

fof(f2107,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tops_1)).

fof(f3008,plain,(
    v4_pre_topc(sK30,sK29) ),
    inference(cnf_transformation,[],[f2731])).
%------------------------------------------------------------------------------
