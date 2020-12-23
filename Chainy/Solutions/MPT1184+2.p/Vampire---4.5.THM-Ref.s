%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1184+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 4.62s
% Output     : Refutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 127 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 829 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9597,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9592,f6662])).

fof(f6662,plain,(
    ~ v6_orders_2(sK48,sK47) ),
    inference(resolution,[],[f4226,f4224])).

fof(f4224,plain,(
    m1_subset_1(sK48,k1_zfmisc_1(u1_struct_0(sK47))) ),
    inference(cnf_transformation,[],[f3283])).

fof(f3283,plain,
    ( ( ~ m1_subset_1(sK48,k1_zfmisc_1(u1_struct_0(sK47)))
      | ~ v6_orders_2(sK48,sK47) )
    & r3_orders_1(u1_orders_2(sK47),sK48)
    & m1_subset_1(sK48,k1_zfmisc_1(u1_struct_0(sK47)))
    & l1_orders_2(sK47)
    & v5_orders_2(sK47)
    & v4_orders_2(sK47)
    & v3_orders_2(sK47)
    & ~ v2_struct_0(sK47) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK47,sK48])],[f2014,f3282,f3281])).

fof(f3281,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK47)))
            | ~ v6_orders_2(X1,sK47) )
          & r3_orders_1(u1_orders_2(sK47),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK47))) )
      & l1_orders_2(sK47)
      & v5_orders_2(sK47)
      & v4_orders_2(sK47)
      & v3_orders_2(sK47)
      & ~ v2_struct_0(sK47) ) ),
    introduced(choice_axiom,[])).

fof(f3282,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK47)))
          | ~ v6_orders_2(X1,sK47) )
        & r3_orders_1(u1_orders_2(sK47),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK47))) )
   => ( ( ~ m1_subset_1(sK48,k1_zfmisc_1(u1_struct_0(sK47)))
        | ~ v6_orders_2(sK48,sK47) )
      & r3_orders_1(u1_orders_2(sK47),sK48)
      & m1_subset_1(sK48,k1_zfmisc_1(u1_struct_0(sK47))) ) ),
    introduced(choice_axiom,[])).

fof(f2014,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2013])).

fof(f2013,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1927])).

fof(f1927,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1926])).

fof(f1926,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r3_orders_1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_orders_2)).

fof(f4226,plain,
    ( ~ m1_subset_1(sK48,k1_zfmisc_1(u1_struct_0(sK47)))
    | ~ v6_orders_2(sK48,sK47) ),
    inference(cnf_transformation,[],[f3283])).

fof(f9592,plain,(
    v6_orders_2(sK48,sK47) ),
    inference(resolution,[],[f9297,f6466])).

fof(f6466,plain,
    ( ~ r7_relat_2(u1_orders_2(sK47),sK48)
    | v6_orders_2(sK48,sK47) ),
    inference(subsumption_resolution,[],[f6388,f4223])).

fof(f4223,plain,(
    l1_orders_2(sK47) ),
    inference(cnf_transformation,[],[f3283])).

fof(f6388,plain,
    ( ~ r7_relat_2(u1_orders_2(sK47),sK48)
    | v6_orders_2(sK48,sK47)
    | ~ l1_orders_2(sK47) ),
    inference(resolution,[],[f4224,f4269])).

fof(f4269,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3304])).

fof(f3304,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2036])).

fof(f2036,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1864])).

fof(f1864,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f9297,plain,(
    r7_relat_2(u1_orders_2(sK47),sK48) ),
    inference(subsumption_resolution,[],[f9296,f8639])).

fof(f8639,plain,(
    v1_relat_1(u1_orders_2(sK47)) ),
    inference(resolution,[],[f6374,f4317])).

fof(f4317,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2076])).

fof(f2076,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f6374,plain,(
    m1_subset_1(u1_orders_2(sK47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK47),u1_struct_0(sK47)))) ),
    inference(resolution,[],[f4223,f4302])).

fof(f4302,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2060,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1897])).

fof(f1897,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f9296,plain,
    ( r7_relat_2(u1_orders_2(sK47),sK48)
    | ~ v1_relat_1(u1_orders_2(sK47)) ),
    inference(subsumption_resolution,[],[f9292,f8774])).

fof(f8774,plain,(
    r6_relat_2(u1_orders_2(sK47),sK48) ),
    inference(resolution,[],[f8639,f6380])).

fof(f6380,plain,
    ( ~ v1_relat_1(u1_orders_2(sK47))
    | r6_relat_2(u1_orders_2(sK47),sK48) ),
    inference(resolution,[],[f4225,f4276])).

fof(f4276,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_1(X0,X1)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3306])).

fof(f3306,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3305])).

fof(f3305,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2041])).

fof(f2041,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f1879,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

fof(f4225,plain,(
    r3_orders_1(u1_orders_2(sK47),sK48) ),
    inference(cnf_transformation,[],[f3283])).

fof(f9292,plain,
    ( ~ r6_relat_2(u1_orders_2(sK47),sK48)
    | r7_relat_2(u1_orders_2(sK47),sK48)
    | ~ v1_relat_1(u1_orders_2(sK47)) ),
    inference(resolution,[],[f8777,f5363])).

fof(f5363,plain,(
    ! [X0,X1] :
      ( ~ r1_relat_2(X1,X0)
      | ~ r6_relat_2(X1,X0)
      | r7_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3917])).

fof(f3917,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f3916])).

fof(f3916,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2711])).

fof(f2711,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1976])).

fof(f1976,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(f8777,plain,(
    r1_relat_2(u1_orders_2(sK47),sK48) ),
    inference(resolution,[],[f8639,f6377])).

fof(f6377,plain,
    ( ~ v1_relat_1(u1_orders_2(sK47))
    | r1_relat_2(u1_orders_2(sK47),sK48) ),
    inference(resolution,[],[f4225,f4273])).

fof(f4273,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_1(X0,X1)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3306])).
%------------------------------------------------------------------------------
