%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t57_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 4.75s
% Output     : Refutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  161 (1585 expanded)
%              Number of leaves         :   24 ( 730 expanded)
%              Depth                    :   18
%              Number of atoms          :  638 (21117 expanded)
%              Number of equality atoms :   77 (1812 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52370,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52232,f319])).

fof(f319,plain,(
    ~ v4_pre_topc(k10_relat_1(sK2,sK5(sK0,sK3,sK2)),sK0) ),
    inference(backward_demodulation,[],[f308,f257])).

fof(f257,plain,(
    ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f256,f118])).

fof(f118,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,
    ( ~ v5_pre_topc(sK4,sK0,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & v5_pre_topc(sK2,sK0,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f55,f97,f96,f95,f94,f93])).

fof(f93,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v5_pre_topc(X4,X0,X3)
                        & X2 = X4
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & v5_pre_topc(X2,X0,X1)
                    & m1_pre_topc(X3,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,sK0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,sK0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,X0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(X4,X0,X3)
                    & X2 = X4
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                & v5_pre_topc(X2,X0,sK1)
                & m1_pre_topc(X3,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v5_pre_topc(X4,X0,X3)
                  & X2 = X4
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                  & v1_funct_1(X4) )
              & v5_pre_topc(X2,X0,X1)
              & m1_pre_topc(X3,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(X4,X0,X3)
                & sK2 = X4
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & v5_pre_topc(sK2,X0,X1)
            & m1_pre_topc(X3,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ v5_pre_topc(X4,X0,X3)
              & X2 = X4
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & v5_pre_topc(X2,X0,X1)
          & m1_pre_topc(X3,X1) )
     => ( ? [X4] :
            ( ~ v5_pre_topc(X4,X0,sK3)
            & X2 = X4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & v5_pre_topc(X2,X0,X1)
        & m1_pre_topc(sK3,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( ~ v5_pre_topc(X4,X0,X3)
          & X2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          & v1_funct_1(X4) )
     => ( ~ v5_pre_topc(sK4,X0,X3)
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X3))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,X0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,X0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_pre_topc(X3,X1)
                   => ( v5_pre_topc(X2,X0,X1)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( X2 = X4
                           => v5_pre_topc(X4,X0,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X1)
                 => ( v5_pre_topc(X2,X0,X1)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                       => ( X2 = X4
                         => v5_pre_topc(X4,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t57_pre_topc)).

fof(f256,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f255,f230])).

fof(f230,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f225,f121])).

fof(f121,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f225,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f125,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',dt_m1_pre_topc)).

fof(f125,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f255,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f254,f185])).

fof(f185,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f127,f130])).

fof(f130,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f98])).

fof(f127,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f98])).

fof(f254,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f253,f184])).

fof(f184,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f128,f130])).

fof(f128,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f98])).

fof(f253,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f242,f183])).

fof(f183,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f129,f130])).

fof(f129,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f98])).

fof(f242,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f182,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v4_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f100,f101])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',d12_pre_topc)).

fof(f182,plain,(
    ~ v5_pre_topc(sK2,sK0,sK3) ),
    inference(backward_demodulation,[],[f130,f131])).

fof(f131,plain,(
    ~ v5_pre_topc(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f98])).

fof(f308,plain,(
    ! [X2] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,X2) = k10_relat_1(sK2,X2) ),
    inference(resolution,[],[f183,f178])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',redefinition_k8_relset_1)).

fof(f52232,plain,(
    v4_pre_topc(k10_relat_1(sK2,sK5(sK0,sK3,sK2)),sK0) ),
    inference(backward_demodulation,[],[f52134,f1492])).

fof(f1492,plain,(
    v4_pre_topc(k10_relat_1(sK2,sK6(sK1,sK3,sK5(sK0,sK3,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f1478,f780])).

fof(f780,plain,(
    m1_subset_1(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f772,f247])).

fof(f247,plain,(
    m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f246,f118])).

fof(f246,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f245,f230])).

fof(f245,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f244,f185])).

fof(f244,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f243,f184])).

fof(f243,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f240,f183])).

fof(f240,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f182,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f772,plain,
    ( m1_subset_1(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f226,f252])).

fof(f252,plain,(
    v4_pre_topc(sK5(sK0,sK3,sK2),sK3) ),
    inference(subsumption_resolution,[],[f251,f118])).

fof(f251,plain,
    ( v4_pre_topc(sK5(sK0,sK3,sK2),sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f250,f230])).

fof(f250,plain,
    ( v4_pre_topc(sK5(sK0,sK3,sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f249,f185])).

fof(f249,plain,
    ( v4_pre_topc(sK5(sK0,sK3,sK2),sK3)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f248,f184])).

fof(f248,plain,
    ( v4_pre_topc(sK5(sK0,sK3,sK2),sK3)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f241,f183])).

fof(f241,plain,
    ( v4_pre_topc(sK5(sK0,sK3,sK2),sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f182,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f226,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK3)
      | m1_subset_1(sK6(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f221,f121])).

fof(f221,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f125,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f104,f105])).

fof(f105,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t43_pre_topc)).

fof(f1478,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK6(sK1,sK3,sK5(sK0,sK3,sK2))),sK0)
    | ~ m1_subset_1(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f752,f293])).

fof(f293,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(backward_demodulation,[],[f281,f236])).

fof(f236,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f235,f118])).

fof(f235,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f121])).

fof(f234,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f185])).

fof(f233,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f123])).

fof(f123,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f98])).

fof(f232,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f124])).

fof(f124,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f98])).

fof(f231,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f126,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f126,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f281,plain,(
    ! [X2] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2) = k10_relat_1(sK2,X2) ),
    inference(resolution,[],[f124,f178])).

fof(f752,plain,(
    v4_pre_topc(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f744,f247])).

fof(f744,plain,
    ( v4_pre_topc(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f227,f252])).

fof(f227,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK3)
      | v4_pre_topc(sK6(sK1,sK3,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f222,f121])).

fof(f222,plain,(
    ! [X1] :
      ( v4_pre_topc(sK6(sK1,sK3,X1),sK1)
      | ~ v4_pre_topc(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f125,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK6(X0,X1,X2),X0)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f52134,plain,(
    k10_relat_1(sK2,sK5(sK0,sK3,sK2)) = k10_relat_1(sK2,sK6(sK1,sK3,sK5(sK0,sK3,sK2))) ),
    inference(superposition,[],[f3708,f1148])).

fof(f1148,plain,(
    k3_xboole_0(u1_struct_0(sK3),sK6(sK1,sK3,sK5(sK0,sK3,sK2))) = sK5(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f1140,f247])).

fof(f1140,plain,
    ( k3_xboole_0(u1_struct_0(sK3),sK6(sK1,sK3,sK5(sK0,sK3,sK2))) = sK5(sK0,sK3,sK2)
    | ~ m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f1126,f252])).

fof(f1126,plain,(
    ! [X2] :
      ( ~ v4_pre_topc(X2,sK3)
      | k3_xboole_0(u1_struct_0(sK3),sK6(sK1,sK3,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(forward_demodulation,[],[f1100,f150])).

fof(f150,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',commutativity_k3_xboole_0)).

fof(f1100,plain,(
    ! [X2] :
      ( k3_xboole_0(sK6(sK1,sK3,X2),u1_struct_0(sK3)) = X2
      | ~ v4_pre_topc(X2,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(backward_demodulation,[],[f1083,f369])).

fof(f369,plain,(
    ! [X2] :
      ( ~ v4_pre_topc(X2,sK3)
      | k9_subset_1(u1_struct_0(sK3),sK6(sK1,sK3,X2),u1_struct_0(sK3)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(backward_demodulation,[],[f366,f228])).

fof(f228,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK6(sK1,sK3,X2),k2_struct_0(sK3)) = X2
      | ~ v4_pre_topc(X2,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f223,f121])).

fof(f223,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK6(sK1,sK3,X2),k2_struct_0(sK3)) = X2
      | ~ v4_pre_topc(X2,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f125,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f366,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f323,f135])).

fof(f135,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',d3_struct_0)).

fof(f323,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f230,f137])).

fof(f137,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',dt_l1_pre_topc)).

fof(f1083,plain,(
    ! [X8] : k3_xboole_0(X8,u1_struct_0(sK3)) = k9_subset_1(u1_struct_0(sK3),X8,u1_struct_0(sK3)) ),
    inference(resolution,[],[f367,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',redefinition_k9_subset_1)).

fof(f367,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(backward_demodulation,[],[f366,f365])).

fof(f365,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f323,f136])).

fof(f136,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',dt_k2_struct_0)).

fof(f3708,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK3),X0)) ),
    inference(forward_demodulation,[],[f3695,f1059])).

fof(f1059,plain,(
    ! [X1] : k3_xboole_0(k1_relat_1(sK2),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,X1) ),
    inference(forward_demodulation,[],[f1058,f341])).

fof(f341,plain,(
    ! [X4] : k10_relat_1(sK2,X4) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X4)) ),
    inference(resolution,[],[f273,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t168_relat_1)).

fof(f273,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f124,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',cc1_relset_1)).

fof(f1058,plain,(
    ! [X1] : k3_xboole_0(k1_relat_1(sK2),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X1)) ),
    inference(subsumption_resolution,[],[f1057,f273])).

fof(f1057,plain,(
    ! [X1] :
      ( k3_xboole_0(k1_relat_1(sK2),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1052,f185])).

fof(f1052,plain,(
    ! [X1] :
      ( k3_xboole_0(k1_relat_1(sK2),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f174,f343])).

fof(f343,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f273,f134])).

fof(f134,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t169_relat_1)).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t137_funct_1)).

fof(f3695,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK3),X0)) ),
    inference(superposition,[],[f344,f3171])).

fof(f3171,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f3170,f343])).

fof(f3170,plain,(
    k10_relat_1(sK2,u1_struct_0(sK3)) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f3163,f273])).

fof(f3163,plain,
    ( k10_relat_1(sK2,u1_struct_0(sK3)) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f152,f879])).

fof(f879,plain,(
    k3_xboole_0(k2_relat_1(sK2),u1_struct_0(sK3)) = k2_relat_1(sK2) ),
    inference(resolution,[],[f374,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',t28_xboole_1)).

fof(f374,plain,(
    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f373,f273])).

fof(f373,plain,
    ( r1_tarski(k2_relat_1(sK2),u1_struct_0(sK3))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f306,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',d19_relat_1)).

fof(f306,plain,(
    v5_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(resolution,[],[f183,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t57_pre_topc.p',cc2_relset_1)).

fof(f344,plain,(
    ! [X0,X1] : k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f338,f185])).

fof(f338,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f273,f174])).
%------------------------------------------------------------------------------
