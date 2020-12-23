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
% DateTime   : Thu Dec  3 13:19:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 (1126 expanded)
%              Number of leaves         :    9 ( 294 expanded)
%              Depth                    :   28
%              Number of atoms          :  534 (10440 expanded)
%              Number of equality atoms :   96 (1786 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(subsumption_resolution,[],[f276,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k8_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( k8_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f276,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f275,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f275,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f274,f35])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f274,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f273,f145])).

fof(f145,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f135,f33])).

fof(f135,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f273,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f272,f271])).

fof(f271,plain,(
    v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f270,f259])).

fof(f259,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f258,f194])).

fof(f194,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f193,f32])).

fof(f193,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f192,f33])).

fof(f192,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f191,f145])).

fof(f191,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f190,f35])).

fof(f190,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f36,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f36,plain,
    ( v1_tsep_1(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f258,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f257,f170])).

fof(f170,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f169,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f169,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f32])).

fof(f168,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f33])).

fof(f167,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f157])).

fof(f157,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f156,f31])).

fof(f156,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f32])).

fof(f155,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f33])).

fof(f139,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f166,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f160])).

fof(f160,plain,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f159,f31])).

fof(f159,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f32])).

fof(f158,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f140,f33])).

fof(f140,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f165,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f163])).

fof(f163,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f162,f31])).

fof(f162,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f32])).

fof(f161,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f33])).

fof(f141,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f164,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f145])).

fof(f142,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f257,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f256,f31])).

fof(f256,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f32])).

fof(f255,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f33])).

fof(f253,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f145,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f270,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f269,f170])).

fof(f269,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f268,f31])).

fof(f268,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f267,f32])).

fof(f267,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f33])).

fof(f254,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f145,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f272,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f266,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f266,plain,(
    ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f265,f35])).

fof(f265,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f38,f259])).

fof(f38,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (18365)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.45  % (18361)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (18379)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.45  % (18365)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (18369)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (18381)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (18381)Refutation not found, incomplete strategy% (18381)------------------------------
% 0.21/0.46  % (18381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (18381)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (18381)Memory used [KB]: 10618
% 0.21/0.46  % (18381)Time elapsed: 0.049 s
% 0.21/0.46  % (18381)------------------------------
% 0.21/0.46  % (18381)------------------------------
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f277,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f276,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k8_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ? [X1] : ((k8_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (((k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.21/0.46  fof(f276,plain,(
% 0.21/0.46    ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f275,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f275,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f274,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    m1_pre_topc(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f274,plain,(
% 0.21/0.46    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f273,f145])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f135,f33])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.46    inference(resolution,[],[f35,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.46  fof(f273,plain,(
% 0.21/0.46    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f272,f271])).
% 0.21/0.46  fof(f271,plain,(
% 0.21/0.46    v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f270,f259])).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f258,f194])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f193,f32])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f192,f33])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f191,f145])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f190,f35])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(resolution,[],[f36,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v1_tsep_1(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f258,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.46    inference(forward_demodulation,[],[f257,f170])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f169,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f168,f32])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f167,f33])).
% 0.21/0.46  fof(f167,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f166,f157])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f156,f31])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    v1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f155,f32])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f139,f33])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f35,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f165,f160])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f159,f31])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f158,f32])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f140,f33])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f35,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f164,f163])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f162,f31])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f161,f32])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f141,f33])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f35,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f142,f145])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f35,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(rectify,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 0.21/0.46  fof(f257,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f256,f31])).
% 0.21/0.46  fof(f256,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f255,f32])).
% 0.21/0.46  fof(f255,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f253,f33])).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f145,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.21/0.46  fof(f270,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.46    inference(forward_demodulation,[],[f269,f170])).
% 0.21/0.46  fof(f269,plain,(
% 0.21/0.46    v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f268,f31])).
% 0.21/0.46  fof(f268,plain,(
% 0.21/0.46    v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f267,f32])).
% 0.21/0.46  fof(f267,plain,(
% 0.21/0.46    v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f254,f33])).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f145,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f272,plain,(
% 0.21/0.46    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(resolution,[],[f266,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    ~v1_tsep_1(sK1,sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f265,f35])).
% 0.21/0.46  fof(f265,plain,(
% 0.21/0.46    ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f260])).
% 0.21/0.46  fof(f260,plain,(
% 0.21/0.46    k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.46    inference(backward_demodulation,[],[f38,f259])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ~m1_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (18365)------------------------------
% 0.21/0.46  % (18365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (18365)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (18365)Memory used [KB]: 1791
% 0.21/0.46  % (18365)Time elapsed: 0.052 s
% 0.21/0.46  % (18365)------------------------------
% 0.21/0.46  % (18365)------------------------------
% 0.21/0.47  % (18360)Success in time 0.102 s
%------------------------------------------------------------------------------
