%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:26 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 498 expanded)
%              Number of leaves         :    8 ( 132 expanded)
%              Depth                    :   10
%              Number of atoms          :  321 (4816 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f52,f58,f53,f62,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | v3_pre_topc(X1,X0)
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f62,plain,(
    v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f57,f59,f58,f60,f61,f31])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(X2,sK0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v1_tdlat_3(sK0)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,sK0,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ~ v1_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X0,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v1_tdlat_3(sK0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,sK0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X0,X1) ) )
         => v1_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tex_2)).

fof(f61,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f46])).

fof(f60,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f45])).

fof(f59,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f57,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f55,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f29,f32,f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f32,plain,(
    ~ v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ~ v3_pre_topc(sK1(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f30,f32,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK1(X0),X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:07 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (738000897)
% 0.21/0.37  ipcrm: permission denied for id (738033666)
% 0.21/0.38  ipcrm: permission denied for id (738230280)
% 0.21/0.38  ipcrm: permission denied for id (738394125)
% 0.21/0.39  ipcrm: permission denied for id (738459664)
% 0.21/0.39  ipcrm: permission denied for id (738492433)
% 0.21/0.39  ipcrm: permission denied for id (738525203)
% 0.21/0.39  ipcrm: permission denied for id (738590742)
% 0.21/0.40  ipcrm: permission denied for id (738689049)
% 0.21/0.40  ipcrm: permission denied for id (738754586)
% 0.21/0.40  ipcrm: permission denied for id (738852894)
% 0.21/0.41  ipcrm: permission denied for id (738918431)
% 0.21/0.41  ipcrm: permission denied for id (739016738)
% 0.21/0.42  ipcrm: permission denied for id (739213353)
% 0.21/0.42  ipcrm: permission denied for id (739278892)
% 0.21/0.43  ipcrm: permission denied for id (739344431)
% 0.21/0.43  ipcrm: permission denied for id (739377200)
% 0.21/0.43  ipcrm: permission denied for id (739409970)
% 0.21/0.43  ipcrm: permission denied for id (739442739)
% 0.21/0.43  ipcrm: permission denied for id (739475508)
% 0.21/0.44  ipcrm: permission denied for id (739606584)
% 0.21/0.44  ipcrm: permission denied for id (739672122)
% 0.21/0.44  ipcrm: permission denied for id (739770429)
% 0.21/0.45  ipcrm: permission denied for id (739868736)
% 0.21/0.45  ipcrm: permission denied for id (740065350)
% 0.21/0.45  ipcrm: permission denied for id (740098119)
% 0.21/0.46  ipcrm: permission denied for id (740196426)
% 0.21/0.46  ipcrm: permission denied for id (740229196)
% 0.21/0.46  ipcrm: permission denied for id (740327503)
% 0.21/0.47  ipcrm: permission denied for id (740360272)
% 0.21/0.47  ipcrm: permission denied for id (740393041)
% 0.21/0.47  ipcrm: permission denied for id (740458579)
% 0.21/0.47  ipcrm: permission denied for id (740491348)
% 0.21/0.48  ipcrm: permission denied for id (740622424)
% 0.21/0.48  ipcrm: permission denied for id (740655193)
% 0.21/0.48  ipcrm: permission denied for id (740720732)
% 0.21/0.48  ipcrm: permission denied for id (740753501)
% 0.21/0.48  ipcrm: permission denied for id (740786270)
% 0.21/0.49  ipcrm: permission denied for id (740884578)
% 0.21/0.49  ipcrm: permission denied for id (740982886)
% 0.21/0.50  ipcrm: permission denied for id (741048425)
% 0.21/0.50  ipcrm: permission denied for id (741081195)
% 0.21/0.50  ipcrm: permission denied for id (741113965)
% 0.21/0.50  ipcrm: permission denied for id (741179503)
% 0.21/0.50  ipcrm: permission denied for id (741212272)
% 0.21/0.51  ipcrm: permission denied for id (741343350)
% 0.21/0.51  ipcrm: permission denied for id (741441657)
% 0.21/0.52  ipcrm: permission denied for id (741572732)
% 0.21/0.52  ipcrm: permission denied for id (741638269)
% 0.21/0.52  ipcrm: permission denied for id (741671038)
% 0.59/0.59  % (21117)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.82/0.60  % (21127)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.82/0.61  % (21127)Refutation found. Thanks to Tanya!
% 0.82/0.61  % SZS status Theorem for theBenchmark
% 0.82/0.61  % SZS output start Proof for theBenchmark
% 0.82/0.61  fof(f70,plain,(
% 0.82/0.61    $false),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f52,f58,f53,f62,f51])).
% 0.82/0.61  fof(f51,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | v3_pre_topc(X1,X0) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(subsumption_resolution,[],[f50,f45])).
% 0.82/0.61  fof(f45,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f17])).
% 0.82/0.61  fof(f17,plain,(
% 0.82/0.61    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.82/0.61    inference(flattening,[],[f16])).
% 0.82/0.61  fof(f16,plain,(
% 0.82/0.61    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.82/0.61    inference(ennf_transformation,[],[f2])).
% 0.82/0.61  fof(f2,axiom,(
% 0.82/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.82/0.61  fof(f50,plain,(
% 0.82/0.61    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(subsumption_resolution,[],[f37,f46])).
% 0.82/0.61  fof(f46,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f17])).
% 0.82/0.61  fof(f37,plain,(
% 0.82/0.61    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f23])).
% 0.82/0.61  fof(f23,plain,(
% 0.82/0.61    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.82/0.61    inference(flattening,[],[f22])).
% 0.82/0.61  fof(f22,plain,(
% 0.82/0.61    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.82/0.61    inference(nnf_transformation,[],[f11])).
% 0.82/0.61  fof(f11,plain,(
% 0.82/0.61    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.82/0.61    inference(flattening,[],[f10])).
% 0.82/0.61  fof(f10,plain,(
% 0.82/0.61    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.82/0.61    inference(ennf_transformation,[],[f4])).
% 0.82/0.61  fof(f4,axiom,(
% 0.82/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 0.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 0.82/0.61  fof(f62,plain,(
% 0.82/0.61    v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0)))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f55,f57,f59,f58,f60,f61,f31])).
% 0.82/0.61  fof(f31,plain,(
% 0.82/0.61    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X2,sK0,X1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f21])).
% 0.82/0.61  fof(f21,plain,(
% 0.82/0.61    ~v1_tdlat_3(sK0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).
% 0.82/0.61  fof(f20,plain,(
% 0.82/0.61    ? [X0] : (~v1_tdlat_3(X0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (~v1_tdlat_3(sK0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.82/0.61    introduced(choice_axiom,[])).
% 0.82/0.61  fof(f9,plain,(
% 0.82/0.61    ? [X0] : (~v1_tdlat_3(X0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.82/0.61    inference(flattening,[],[f8])).
% 0.82/0.61  fof(f8,plain,(
% 0.82/0.61    ? [X0] : ((~v1_tdlat_3(X0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,X0,X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.82/0.61    inference(ennf_transformation,[],[f7])).
% 0.82/0.61  fof(f7,negated_conjecture,(
% 0.82/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))) => v1_tdlat_3(X0)))),
% 0.82/0.61    inference(negated_conjecture,[],[f6])).
% 0.82/0.61  fof(f6,conjecture,(
% 0.82/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))) => v1_tdlat_3(X0)))),
% 0.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tex_2)).
% 0.82/0.61  fof(f61,plain,(
% 0.82/0.61    m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f46])).
% 0.82/0.61  fof(f60,plain,(
% 0.82/0.61    v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f45])).
% 0.82/0.61  fof(f59,plain,(
% 0.82/0.61    l1_pre_topc(k6_tmap_1(sK0,sK1(sK0)))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f49])).
% 0.82/0.61  fof(f49,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f19])).
% 0.82/0.61  fof(f19,plain,(
% 0.82/0.61    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.82/0.61    inference(flattening,[],[f18])).
% 0.82/0.61  fof(f18,plain,(
% 0.82/0.61    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.82/0.61    inference(ennf_transformation,[],[f1])).
% 0.82/0.61  fof(f1,axiom,(
% 0.82/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.82/0.61  fof(f57,plain,(
% 0.82/0.61    v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f43])).
% 0.82/0.61  fof(f43,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f15])).
% 0.82/0.61  fof(f15,plain,(
% 0.82/0.61    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.82/0.61    inference(flattening,[],[f14])).
% 0.82/0.61  fof(f14,plain,(
% 0.82/0.61    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.82/0.61    inference(ennf_transformation,[],[f3])).
% 0.82/0.61  fof(f3,axiom,(
% 0.82/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 0.82/0.61  fof(f55,plain,(
% 0.82/0.61    ~v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f41])).
% 0.82/0.61  fof(f41,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f15])).
% 0.82/0.61  fof(f53,plain,(
% 0.82/0.61    m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f29,f32,f30,f39])).
% 0.82/0.61  fof(f39,plain,(
% 0.82/0.61    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | v1_tdlat_3(X0) | ~v2_pre_topc(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f27])).
% 0.82/0.61  fof(f27,plain,(
% 0.82/0.61    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 0.82/0.61  fof(f26,plain,(
% 0.82/0.61    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.82/0.61    introduced(choice_axiom,[])).
% 0.82/0.61  fof(f25,plain,(
% 0.82/0.61    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.82/0.61    inference(rectify,[],[f24])).
% 0.82/0.61  fof(f24,plain,(
% 0.82/0.61    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.82/0.61    inference(nnf_transformation,[],[f13])).
% 0.82/0.61  fof(f13,plain,(
% 0.82/0.61    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.82/0.61    inference(flattening,[],[f12])).
% 0.82/0.61  fof(f12,plain,(
% 0.82/0.61    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.82/0.61    inference(ennf_transformation,[],[f5])).
% 0.82/0.61  fof(f5,axiom,(
% 0.82/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.82/0.61  fof(f32,plain,(
% 0.82/0.61    ~v1_tdlat_3(sK0)),
% 0.82/0.61    inference(cnf_transformation,[],[f21])).
% 0.82/0.61  fof(f58,plain,(
% 0.82/0.61    v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f28,f29,f30,f53,f44])).
% 0.82/0.61  fof(f44,plain,(
% 0.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f17])).
% 0.82/0.61  fof(f52,plain,(
% 0.82/0.61    ~v3_pre_topc(sK1(sK0),sK0)),
% 0.82/0.61    inference(unit_resulting_resolution,[],[f29,f30,f32,f40])).
% 0.82/0.61  fof(f40,plain,(
% 0.82/0.61    ( ! [X0] : (~v3_pre_topc(sK1(X0),X0) | v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.82/0.61    inference(cnf_transformation,[],[f27])).
% 0.82/0.61  fof(f30,plain,(
% 0.82/0.61    l1_pre_topc(sK0)),
% 0.82/0.61    inference(cnf_transformation,[],[f21])).
% 0.82/0.61  fof(f29,plain,(
% 0.82/0.61    v2_pre_topc(sK0)),
% 0.82/0.61    inference(cnf_transformation,[],[f21])).
% 0.82/0.61  fof(f28,plain,(
% 0.82/0.61    ~v2_struct_0(sK0)),
% 0.82/0.61    inference(cnf_transformation,[],[f21])).
% 0.82/0.61  % SZS output end Proof for theBenchmark
% 0.82/0.61  % (21127)------------------------------
% 0.82/0.61  % (21127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.82/0.61  % (21127)Termination reason: Refutation
% 0.82/0.61  
% 0.82/0.61  % (21127)Memory used [KB]: 5373
% 0.82/0.61  % (21127)Time elapsed: 0.007 s
% 0.82/0.61  % (21127)------------------------------
% 0.82/0.61  % (21127)------------------------------
% 0.82/0.61  % (20974)Success in time 0.249 s
%------------------------------------------------------------------------------
