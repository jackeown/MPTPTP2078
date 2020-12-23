%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1145+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 13.75s
% Output     : Refutation 14.34s
% Verified   : 
% Statistics : Number of formulae       :   37 (  74 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 336 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8170,f3464])).

fof(f3464,plain,(
    ~ r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(subsumption_resolution,[],[f3463,f2434])).

fof(f2434,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1906])).

fof(f1906,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f1905])).

fof(f1905,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1894])).

fof(f1894,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,X1)
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_orders_2)).

fof(f3463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(subsumption_resolution,[],[f3460,f2438])).

fof(f2438,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1906])).

fof(f3460,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(resolution,[],[f3327,f2574])).

fof(f2574,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2001])).

fof(f2001,plain,(
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

fof(f3327,plain,(
    ~ v6_orders_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f2433,f2434])).

fof(f2433,plain,
    ( ~ v6_orders_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1906])).

fof(f8170,plain,(
    r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(subsumption_resolution,[],[f8157,f3458])).

fof(f3458,plain,(
    r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f3457,f2437])).

fof(f2437,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1906])).

fof(f3457,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f3456,f2438])).

fof(f3456,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f2436,f2575])).

fof(f2575,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2001])).

fof(f2436,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f1906])).

fof(f8157,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(resolution,[],[f7636,f3446])).

fof(f3446,plain,(
    ! [X66] :
      ( ~ v1_relat_1(X66)
      | ~ r7_relat_2(X66,sK1)
      | r7_relat_2(X66,sK2) ) ),
    inference(resolution,[],[f2435,f3235])).

fof(f3235,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r7_relat_2(X2,X0)
      | ~ r1_tarski(X1,X0)
      | r7_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f2419])).

fof(f2419,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2418])).

fof(f2418,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1896])).

fof(f1896,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r7_relat_2(X2,X0) )
       => r7_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_orders_1)).

fof(f2435,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f1906])).

fof(f7636,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f3352,f2528])).

fof(f2528,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1970])).

fof(f1970,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3352,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f2438,f3247])).

fof(f3247,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f2424])).

fof(f2424,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1874])).

fof(f1874,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
%------------------------------------------------------------------------------
