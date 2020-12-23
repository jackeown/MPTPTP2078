%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1796+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 (3582 expanded)
%              Number of leaves         :   11 ( 634 expanded)
%              Depth                    :   37
%              Number of atoms          :  688 (25879 expanded)
%              Number of equality atoms :   17 (2252 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f842,plain,(
    $false ),
    inference(global_subsumption,[],[f194,f283,f312,f381,f841])).

fof(f841,plain,(
    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f840,f381])).

fof(f840,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f839,f52])).

fof(f52,plain,(
    sK1 = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( u1_struct_0(X2) = X1
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_tmap_1)).

fof(f839,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f838,f312])).

fof(f838,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f837,f52])).

fof(f837,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f836,f206])).

fof(f206,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f205,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f204,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f173,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f173,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f836,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f835,f283])).

fof(f835,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f834,f92])).

fof(f92,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f90,f56])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f51,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f834,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f833,f94])).

fof(f94,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f93,f55])).

fof(f93,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f91,f56])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f833,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f832,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f832,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f831,f203])).

fof(f203,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f202,f54])).

fof(f202,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f201,f56])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f172,f55])).

fof(f172,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f53,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f831,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f830,f200])).

fof(f200,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f199,f54])).

fof(f199,plain,
    ( v2_struct_0(sK0)
    | v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f198,f56])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f171,f55])).

fof(f171,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f830,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f548,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f548,plain,(
    r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))) ),
    inference(resolution,[],[f547,f272])).

fof(f272,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),X0) ) ),
    inference(forward_demodulation,[],[f271,f187])).

fof(f187,plain,(
    k7_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f186,f54])).

fof(f186,plain,
    ( v2_struct_0(sK0)
    | k7_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f185,f56])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k7_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f169,f55])).

fof(f169,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k7_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f53,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

% (11394)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (11409)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (11410)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
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
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f271,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0) ) ),
    inference(subsumption_resolution,[],[f270,f51])).

fof(f270,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0) ) ),
    inference(subsumption_resolution,[],[f269,f54])).

fof(f269,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0) ) ),
    inference(subsumption_resolution,[],[f268,f56])).

fof(f268,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0) ) ),
    inference(subsumption_resolution,[],[f266,f55])).

fof(f266,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0) ) ),
    inference(resolution,[],[f165,f53])).

fof(f165,plain,(
    ! [X41,X40] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X40)))
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X40)
      | ~ m1_pre_topc(sK2,X40)
      | ~ m1_subset_1(X41,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(X40,sK1),k2_tmap_1(X40,k6_tmap_1(X40,sK1),k7_tmap_1(X40,sK1),sK2),X41) ) ),
    inference(subsumption_resolution,[],[f119,f50])).

fof(f119,plain,(
    ! [X41,X40] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X40)))
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X40)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X40)
      | ~ m1_subset_1(X41,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(X40,sK1),k2_tmap_1(X40,k6_tmap_1(X40,sK1),k7_tmap_1(X40,sK1),sK2),X41) ) ),
    inference(superposition,[],[f85,f52])).

fof(f85,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) != X1
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tmap_1)).

fof(f547,plain,(
    m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1) ),
    inference(global_subsumption,[],[f194,f283,f312,f381,f546])).

fof(f546,plain,
    ( m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f331,f381])).

fof(f331,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f330,f206])).

fof(f330,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f329,f283])).

fof(f329,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f328,f203])).

fof(f328,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f317,f200])).

fof(f317,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f312,f134])).

fof(f134,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(X5,sK1,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X6))))
      | m1_subset_1(sK3(X6,sK2,X5),sK1)
      | v5_pre_topc(X5,sK2,X6) ) ),
    inference(subsumption_resolution,[],[f133,f92])).

fof(f133,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(X5,sK1,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X6))))
      | m1_subset_1(sK3(X6,sK2,X5),sK1)
      | v5_pre_topc(X5,sK2,X6) ) ),
    inference(subsumption_resolution,[],[f132,f94])).

fof(f132,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(X5,sK1,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X6))))
      | m1_subset_1(sK3(X6,sK2,X5),sK1)
      | v5_pre_topc(X5,sK2,X6) ) ),
    inference(subsumption_resolution,[],[f102,f50])).

fof(f102,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(X5,sK1,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X6))))
      | m1_subset_1(sK3(X6,sK2,X5),sK1)
      | v5_pre_topc(X5,sK2,X6) ) ),
    inference(superposition,[],[f61,f52])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f381,plain,(
    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f379,f52])).

fof(f379,plain,(
    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f289,f96])).

fof(f96,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f92,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f289,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ) ),
    inference(resolution,[],[f230,f244])).

fof(f244,plain,(
    l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f203,f77])).

fof(f230,plain,(
    ! [X3] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,sK1))))) ) ),
    inference(subsumption_resolution,[],[f229,f191])).

fof(f191,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f184,f187])).

fof(f184,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f183,f54])).

fof(f183,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f168,f55])).

fof(f168,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f53,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f229,plain,(
    ! [X3] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,sK1))))) ) ),
    inference(subsumption_resolution,[],[f228,f89])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f56,f77])).

fof(f228,plain,(
    ! [X3] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,sK1))))) ) ),
    inference(subsumption_resolution,[],[f212,f189])).

fof(f189,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f178,f187])).

fof(f178,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f177,f54])).

fof(f177,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f176,f56])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f166,f55])).

fof(f166,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f212,plain,(
    ! [X3] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,sK1))))) ) ),
    inference(resolution,[],[f190,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f190,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f181,f187])).

fof(f181,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f180,f54])).

fof(f180,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f179,f56])).

fof(f179,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f167,f55])).

fof(f167,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f53,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f312,plain,(
    v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f310,f52])).

fof(f310,plain,(
    v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f285,f96])).

fof(f285,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0),u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f227,f244])).

fof(f227,plain,(
    ! [X2] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(X2)
      | v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f226,f191])).

fof(f226,plain,(
    ! [X2] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X2)
      | v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f225,f89])).

fof(f225,plain,(
    ! [X2] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X2)
      | v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f211,f189])).

fof(f211,plain,(
    ! [X2] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X2)
      | v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f190,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f283,plain,(
    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)) ),
    inference(resolution,[],[f276,f96])).

fof(f276,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0)) ) ),
    inference(resolution,[],[f224,f244])).

fof(f224,plain,(
    ! [X1] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(X1)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1)) ) ),
    inference(subsumption_resolution,[],[f223,f191])).

fof(f223,plain,(
    ! [X1] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X1)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1)) ) ),
    inference(subsumption_resolution,[],[f222,f89])).

fof(f222,plain,(
    ! [X1] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X1)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1)) ) ),
    inference(subsumption_resolution,[],[f210,f189])).

fof(f210,plain,(
    ! [X1] :
      ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(X1)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1)) ) ),
    inference(resolution,[],[f190,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f194,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)) ),
    inference(forward_demodulation,[],[f193,f187])).

fof(f193,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f192,f187])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f188,f187])).

fof(f188,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f87,f187])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f86,f52])).

fof(f86,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f49,f52])).

fof(f49,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
