%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1634+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 52.26s
% Output     : Refutation 52.26s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 440 expanded)
%              Number of leaves         :    7 (  81 expanded)
%              Depth                    :   23
%              Number of atoms          :  388 (1701 expanded)
%              Number of equality atoms :   24 ( 233 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42888,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41410,f42887])).

fof(f42887,plain,(
    ~ spl14_7 ),
    inference(avatar_contradiction_clause,[],[f42886])).

fof(f42886,plain,
    ( $false
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f42885,f3774])).

fof(f3774,plain,
    ( r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f3773])).

fof(f3773,plain,
    ( spl14_7
  <=> r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f42885,plain,
    ( ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(resolution,[],[f42880,f3373])).

fof(f3373,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2,sK0,sK1),sK1)
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3372,f3225])).

fof(f3225,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3200])).

fof(f3200,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_waybel_0(X0,X1) != a_2_0_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3199])).

fof(f3199,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_waybel_0(X0,X1) != a_2_0_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3185])).

fof(f3185,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3184])).

fof(f3184,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_waybel_0)).

fof(f3372,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | r2_hidden(sK3(X2,sK0,sK1),sK1)
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3363,f3226])).

fof(f3226,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3200])).

fof(f3363,plain,(
    ! [X2] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(sK3(X2,sK0,sK1),sK1)
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3230,f3223])).

fof(f3223,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3200])).

fof(f3230,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3202])).

fof(f3202,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f3201])).

fof(f3201,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3172])).

fof(f3172,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_0)).

fof(f42880,plain,
    ( ~ r2_hidden(sK3(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),sK0,sK1),sK1)
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f42879,f3774])).

fof(f42879,plain,
    ( ~ r2_hidden(sK3(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),sK0,sK1),sK1)
    | ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f42878,f3223])).

fof(f42878,plain,
    ( ~ r2_hidden(sK3(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f42877,f41411])).

fof(f41411,plain,(
    ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f41177,f31044])).

fof(f31044,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
      | r2_hidden(X0,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f12791,f3332])).

fof(f3332,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f3329,f3249])).

fof(f3249,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f3211])).

fof(f3211,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3210])).

fof(f3210,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f3329,plain,(
    m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3325,f3226])).

fof(f3325,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3233,f3223])).

fof(f3233,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f3204])).

fof(f3204,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3203])).

fof(f3203,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3166])).

fof(f3166,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(f12791,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f12790,f3223])).

fof(f12790,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f12779])).

fof(f12779,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3460,f3833])).

fof(f3833,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(sK0,X0,X1),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,a_2_0_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k3_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f3832,f3277])).

fof(f3277,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f3249,f3223])).

fof(f3832,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(sK6(sK0,X0,X1),sK1)
      | r2_hidden(X1,a_2_0_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k3_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f3831,f3226])).

fof(f3831,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(sK6(sK0,X0,X1),sK1)
      | r2_hidden(X1,a_2_0_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X1,k3_waybel_0(sK0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f3828])).

fof(f3828,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(sK6(sK0,X0,X1),sK1)
      | r2_hidden(X1,a_2_0_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X1,k3_waybel_0(sK0,X0)) ) ),
    inference(resolution,[],[f3800,f3272])).

fof(f3272,plain,(
    ! [X0,X3,X1] :
      ( r1_orders_2(X0,X3,sK6(X0,X1,X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f3268,f3233])).

fof(f3268,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK6(X0,X1,X3))
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f3235])).

fof(f3235,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK6(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3205])).

fof(f3205,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3158])).

fof(f3158,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_waybel_0)).

fof(f3800,plain,(
    ! [X6,X7] :
      ( ~ r1_orders_2(sK0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3799,f3225])).

fof(f3799,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3644,f3226])).

fof(f3644,plain,(
    ! [X6,X7] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3265,f3223])).

fof(f3265,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X3,X4)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_0_waybel_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f3227])).

fof(f3227,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X3,X4)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3202])).

fof(f3460,plain,(
    ! [X3] :
      ( r2_hidden(sK6(sK0,sK1,X3),sK1)
      | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3459,f3332])).

fof(f3459,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,sK1,X3),sK1)
      | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3448,f3226])).

fof(f3448,plain,(
    ! [X3] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,sK1,X3),sK1)
      | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3271,f3223])).

fof(f3271,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f3267,f3233])).

fof(f3267,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f3236])).

fof(f3236,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3205])).

fof(f41177,plain,
    ( ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1)) ),
    inference(extensionality_resolution,[],[f3253,f3224])).

fof(f3224,plain,(
    k3_waybel_0(sK0,sK1) != a_2_0_waybel_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f3200])).

fof(f3253,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | ~ r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3213])).

fof(f3213,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f42877,plain,
    ( ~ r2_hidden(sK3(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),sK0,sK1),sK1)
    | r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f42872,f41698])).

fof(f41698,plain,
    ( m1_subset_1(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f41694,f3774])).

fof(f41694,plain,
    ( m1_subset_1(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(superposition,[],[f3444,f41413])).

fof(f41413,plain,
    ( sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)) = sK2(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),sK0,sK1)
    | ~ spl14_7 ),
    inference(resolution,[],[f3774,f3392])).

fof(f3392,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,a_2_0_waybel_0(sK0,sK1))
      | sK2(X2,sK0,sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f3391,f3225])).

fof(f3391,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | sK2(X2,sK0,sK1) = X2
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3382,f3226])).

fof(f3382,plain,(
    ! [X2] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | sK2(X2,sK0,sK1) = X2
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3232,f3223])).

fof(f3232,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3202])).

fof(f3444,plain,(
    ! [X3] :
      ( m1_subset_1(sK2(X3,sK0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3443,f3225])).

fof(f3443,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | m1_subset_1(sK2(X3,sK0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3431,f3226])).

fof(f3431,plain,(
    ! [X3] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(X3,sK0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_0_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3231,f3223])).

fof(f3231,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3202])).

fof(f42872,plain,
    ( ~ m1_subset_1(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),sK0,sK1),sK1)
    | r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | ~ spl14_7 ),
    inference(superposition,[],[f3816,f41413])).

fof(f3816,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2(X2,sK0,X3),u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X2,sK0,X3),sK1)
      | r2_hidden(sK2(X2,sK0,X3),k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3)) ) ),
    inference(subsumption_resolution,[],[f3815,f3277])).

fof(f3815,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3(X2,sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X2,sK0,X3),u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X2,sK0,X3),sK1)
      | r2_hidden(sK2(X2,sK0,X3),k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3)) ) ),
    inference(subsumption_resolution,[],[f3814,f3225])).

fof(f3814,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3(X2,sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X2,sK0,X3),u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X2,sK0,X3),sK1)
      | r2_hidden(sK2(X2,sK0,X3),k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3)) ) ),
    inference(subsumption_resolution,[],[f3809,f3226])).

fof(f3809,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3(X2,sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X2,sK0,X3),u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X2,sK0,X3),sK1)
      | r2_hidden(sK2(X2,sK0,X3),k3_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3)) ) ),
    inference(resolution,[],[f3590,f3229])).

fof(f3229,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2),sK3(X0,X1,X2))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3202])).

fof(f3590,plain,(
    ! [X6,X7] :
      ( ~ r1_orders_2(sK0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,k3_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3580,f3226])).

fof(f3580,plain,(
    ! [X6,X7] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,k3_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3270,f3223])).

fof(f3270,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f3266,f3233])).

fof(f3266,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f3237])).

fof(f3237,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3205])).

fof(f41410,plain,(
    spl14_7 ),
    inference(avatar_contradiction_clause,[],[f41409])).

fof(f41409,plain,
    ( $false
    | spl14_7 ),
    inference(subsumption_resolution,[],[f41400,f3775])).

fof(f3775,plain,
    ( ~ r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | spl14_7 ),
    inference(avatar_component_clause,[],[f3773])).

fof(f41400,plain,
    ( r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),a_2_0_waybel_0(sK0,sK1))
    | spl14_7 ),
    inference(resolution,[],[f41200,f31044])).

fof(f41200,plain,
    ( r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | spl14_7 ),
    inference(subsumption_resolution,[],[f41199,f3224])).

fof(f41199,plain,
    ( r2_hidden(sK10(k3_waybel_0(sK0,sK1),a_2_0_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | k3_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,sK1)
    | spl14_7 ),
    inference(resolution,[],[f3775,f3252])).

fof(f3252,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3213])).
%------------------------------------------------------------------------------
