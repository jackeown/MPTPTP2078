%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  214 (12447 expanded)
%              Number of leaves         :   14 (4284 expanded)
%              Depth                    :   54
%              Number of atoms          : 1031 (79126 expanded)
%              Number of equality atoms :  160 (3121 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(resolution,[],[f400,f146])).

fof(f146,plain,(
    ~ v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f69,f145])).

fof(f145,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f144,f70])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f67,f65])).

fof(f65,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    & v3_tops_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                & v3_tops_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0)
              & v3_tops_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0)
            & v3_tops_2(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),sK1,sK0)
          & v3_tops_2(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),sK1,sK0)
        & v3_tops_2(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      & v3_tops_2(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                 => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f41,f64])).

fof(f64,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f143,f39])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,
    ( ~ v1_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f141,f71])).

fof(f71,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f66,f65])).

fof(f66,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f40,f64])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f95,f139])).

fof(f139,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f138,f70])).

fof(f138,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f137,f39])).

fof(f137,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f136,f36])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f128,f38])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK1)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f71])).

fof(f124,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f123,f64])).

fof(f123,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f122,f65])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f121,f64])).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f120,f65])).

fof(f120,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f119,f64])).

fof(f119,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f118,f65])).

fof(f118,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK2) != X1
      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f94,plain,(
    v2_funct_1(sK2) ),
    inference(resolution,[],[f93,f70])).

fof(f93,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f92,f39])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f91,f36])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f90,f38])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f88,f71])).

fof(f88,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f87,f64])).

fof(f87,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f86,f65])).

fof(f86,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f85,f64])).

fof(f85,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f84,f65])).

fof(f84,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f68,f65])).

fof(f68,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f43,f64])).

fof(f43,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f400,plain,(
    v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f399,f179])).

fof(f179,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f178,f70])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f177,f39])).

fof(f177,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f164,f71])).

fof(f164,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f60,f145])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f399,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f398,f36])).

fof(f398,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f397,f38])).

fof(f397,plain,
    ( ~ l1_pre_topc(sK1)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f396,f169])).

fof(f169,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f168,f70])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f167,f39])).

fof(f167,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f165,f71])).

fof(f165,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f59,f145])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f396,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f395,f115])).

fof(f115,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f107,f70])).

fof(f107,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f106,f39])).

fof(f106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f105,f36])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f104,f38])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f103,f71])).

fof(f103,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f102,f64])).

fof(f102,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f101,f65])).

fof(f101,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f100,f64])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f99,f65])).

fof(f99,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f395,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f394,f294])).

fof(f294,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f293,f179])).

fof(f293,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f292,f148])).

fof(f148,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f77,f145])).

fof(f77,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f76,f71])).

fof(f76,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f75,f70])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,sK2)) ) ),
    inference(resolution,[],[f58,f39])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f292,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f282,f169])).

fof(f282,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f217,f278])).

fof(f278,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f277,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f277,plain,
    ( v2_struct_0(sK1)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f276,f70])).

fof(f276,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f273,f63])).

fof(f273,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f272,f71])).

fof(f272,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f270,f139])).

fof(f270,plain,
    ( k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f269,f145])).

fof(f269,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f251,f65])).

fof(f251,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f250,f64])).

fof(f250,plain,(
    ! [X0] :
      ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f249,f64])).

fof(f249,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f248,f64])).

fof(f248,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f246,f64])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f208,f62])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f170,f39])).

% (31953)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f170,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f47,f94])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f217,plain,(
    ! [X8,X9] :
      ( k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9
      | sK2 = k2_tops_2(X8,X9,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
      | ~ v1_funct_1(k2_funct_1(sK2)) ) ),
    inference(forward_demodulation,[],[f215,f98])).

fof(f98,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f97,f73])).

fof(f73,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f97,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f96,f39])).

fof(f96,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f215,plain,(
    ! [X8,X9] :
      ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2))
      | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
      | ~ v1_funct_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f210,f61])).

fof(f210,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f209,f70])).

fof(f209,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f207,f63])).

fof(f207,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f206,f71])).

fof(f206,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f205])).

fof(f205,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f204,f139])).

fof(f204,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f203,f145])).

fof(f203,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f197,f65])).

fof(f197,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f196,f64])).

fof(f196,plain,(
    ! [X0] :
      ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f195,f64])).

fof(f195,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f194,f64])).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f192,f64])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f183,f62])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f142,f39])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f45,f94])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f394,plain,
    ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f393,f65])).

fof(f393,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f392,f64])).

fof(f392,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f391,f65])).

fof(f391,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f390,f64])).

fof(f390,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f389,f65])).

fof(f389,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f388,f64])).

fof(f388,plain,
    ( v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f387])).

fof(f387,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f386,f265])).

fof(f265,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f263,f37])).

fof(f263,plain,
    ( v2_struct_0(sK1)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f262,f70])).

fof(f262,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f261,f63])).

fof(f261,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f260,f71])).

fof(f260,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f258,f139])).

fof(f258,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f257,f145])).

fof(f257,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f237,f65])).

fof(f237,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f236,f64])).

fof(f236,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f235,f64])).

fof(f235,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f234,f64])).

fof(f234,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f232,f64])).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f189,f62])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f166,f39])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f46,f94])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f386,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f385,f65])).

fof(f385,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f384,f64])).

fof(f384,plain,
    ( v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f382,f278])).

fof(f382,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f381,f65])).

fof(f381,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f380,f64])).

fof(f380,plain,
    ( v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f379,f175])).

fof(f175,plain,(
    v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f174,f70])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f173,f39])).

fof(f173,plain,
    ( ~ v1_funct_1(sK2)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f172,f36])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f171,f38])).

fof(f171,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f154,f71])).

fof(f154,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(backward_demodulation,[],[f135,f145])).

fof(f135,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f134,f64])).

fof(f134,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f133,f65])).

fof(f133,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f132,f64])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f131,f65])).

fof(f131,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f130,f64])).

fof(f130,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f129,f65])).

fof(f129,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f379,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k2_funct_1(sK2),X0,X1)
      | v3_tops_2(k2_funct_1(sK2),X0,X1)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f211,f148])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v5_pre_topc(k2_funct_1(sK2),X0,X1)
      | v3_tops_2(k2_funct_1(sK2),X0,X1)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f210,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | v3_tops_2(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:33:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.50  % (31949)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (31952)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (31970)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (31951)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (31957)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (31968)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (31955)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (31947)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (31967)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (31959)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (31954)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (31950)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (31951)Refutation not found, incomplete strategy% (31951)------------------------------
% 0.22/0.52  % (31951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31951)Memory used [KB]: 10618
% 0.22/0.52  % (31951)Time elapsed: 0.091 s
% 0.22/0.52  % (31951)------------------------------
% 0.22/0.52  % (31951)------------------------------
% 0.22/0.52  % (31969)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (31965)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (31966)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % (31956)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (31971)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (31958)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (31963)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (31964)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  % (31962)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (31961)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (31958)Refutation not found, incomplete strategy% (31958)------------------------------
% 0.22/0.53  % (31958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31958)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31958)Memory used [KB]: 10490
% 0.22/0.53  % (31958)Time elapsed: 0.100 s
% 0.22/0.53  % (31958)------------------------------
% 0.22/0.53  % (31958)------------------------------
% 0.22/0.54  % (31955)Refutation not found, incomplete strategy% (31955)------------------------------
% 0.22/0.54  % (31955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31955)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31955)Memory used [KB]: 6396
% 0.22/0.54  % (31955)Time elapsed: 0.113 s
% 0.22/0.54  % (31955)------------------------------
% 0.22/0.54  % (31955)------------------------------
% 0.22/0.54  % (31957)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f401,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f400,f146])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ~v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    inference(backward_demodulation,[],[f69,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f144,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.54    inference(backward_demodulation,[],[f67,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f44,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    l1_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f49,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    l1_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f32,f31,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),sK1,sK0) & v3_tops_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),sK1,sK0) & v3_tops_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    inference(backward_demodulation,[],[f41,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f44,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    l1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f49,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f143,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.54    inference(resolution,[],[f141,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f66,f65])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f40,f64])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f140])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(superposition,[],[f95,f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.54    inference(resolution,[],[f138,f70])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.54    inference(resolution,[],[f137,f39])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.54    inference(resolution,[],[f136,f36])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.54    inference(resolution,[],[f128,f38])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f124,f71])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f123,f64])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f122,f65])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f121,f64])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f120,f65])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f119,f64])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f118,f65])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f51,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v3_tops_2(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.22/0.54    inference(resolution,[],[f94,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    v2_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f93,f70])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f92,f39])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f91,f36])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f90,f38])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f88,f71])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f87,f64])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f86,f65])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f85,f64])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f84,f65])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f52,f42])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ~v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.54    inference(backward_demodulation,[],[f68,f65])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~v3_tops_2(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.54    inference(backward_demodulation,[],[f43,f64])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f400,plain,(
% 0.22/0.54    v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f399,f179])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.54    inference(resolution,[],[f178,f70])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.54    inference(resolution,[],[f177,f39])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.54    inference(resolution,[],[f164,f71])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(superposition,[],[f60,f145])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.54  fof(f399,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f398,f36])).
% 0.22/0.54  fof(f398,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.54    inference(resolution,[],[f397,f38])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.54    inference(resolution,[],[f396,f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f168,f70])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f167,f39])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.54    inference(resolution,[],[f165,f71])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(superposition,[],[f59,f145])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.54    inference(resolution,[],[f395,f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f107,f70])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f106,f39])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f105,f36])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f104,f38])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f103,f71])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f102,f64])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f101,f65])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f100,f64])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f99,f65])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f53,f42])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f395,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f394,f294])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f293,f179])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f292,f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.54    inference(backward_demodulation,[],[f77,f145])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.54    inference(resolution,[],[f76,f71])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.54    inference(resolution,[],[f75,f70])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_funct_1(k2_tops_2(X0,X1,sK2))) )),
% 0.22/0.54    inference(resolution,[],[f58,f39])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    ~v1_funct_1(k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.54    inference(resolution,[],[f282,f169])).
% 0.22/0.54  fof(f282,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f281])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.54    inference(superposition,[],[f217,f278])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f277,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f277,plain,(
% 0.22/0.54    v2_struct_0(sK1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f276,f70])).
% 0.22/0.54  fof(f276,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f273,f63])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    ~l1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f272,f71])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f271])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f270,f139])).
% 0.22/0.54  fof(f270,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f269,f145])).
% 0.22/0.54  fof(f269,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(superposition,[],[f251,f65])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f250,f64])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    ( ! [X0] : (k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f249,f64])).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f248,f64])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f246,f64])).
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(resolution,[],[f208,f62])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(resolution,[],[f170,f39])).
% 0.22/0.55  % (31953)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_1(sK2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.55    inference(resolution,[],[f47,f94])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    ( ! [X8,X9] : (k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 | sK2 = k2_tops_2(X8,X9,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | ~v1_funct_1(k2_funct_1(sK2))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f215,f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f97,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f72,f70])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f48,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f96,f39])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f94,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ( ! [X8,X9] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2)) | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | ~v1_funct_1(k2_funct_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f210,f61])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f209,f70])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f207,f63])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    ~l1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f206,f71])).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f205])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f204,f139])).
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f203,f145])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.55    inference(superposition,[],[f197,f65])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f196,f64])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    ( ! [X0] : (v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f195,f64])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f194,f64])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f192,f64])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(resolution,[],[f183,f62])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(resolution,[],[f142,f39])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_1(sK2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.55    inference(resolution,[],[f45,f94])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.22/0.55  fof(f394,plain,(
% 0.22/0.55    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f393,f65])).
% 0.22/0.55  fof(f393,plain,(
% 0.22/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f392,f64])).
% 0.22/0.55  fof(f392,plain,(
% 0.22/0.55    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f391,f65])).
% 0.22/0.55  fof(f391,plain,(
% 0.22/0.55    ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f390,f64])).
% 0.22/0.55  fof(f390,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f389,f65])).
% 0.22/0.55  fof(f389,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f388,f64])).
% 0.22/0.55  fof(f388,plain,(
% 0.22/0.55    v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f387])).
% 0.22/0.55  fof(f387,plain,(
% 0.22/0.55    k2_struct_0(sK1) != k2_struct_0(sK1) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f386,f265])).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f263,f37])).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    v2_struct_0(sK1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f262,f70])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.55    inference(resolution,[],[f261,f63])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    ~l1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.55    inference(resolution,[],[f260,f71])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f259])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f258,f139])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f257,f145])).
% 0.22/0.55  fof(f257,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.55    inference(superposition,[],[f237,f65])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f236,f64])).
% 0.22/0.55  fof(f236,plain,(
% 0.22/0.55    ( ! [X0] : (k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f235,f64])).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f234,f64])).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f232,f64])).
% 0.22/0.55  fof(f232,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(resolution,[],[f189,f62])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)) )),
% 0.22/0.55    inference(resolution,[],[f166,f39])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_1(sK2) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_struct_0(X1)) )),
% 0.22/0.55    inference(resolution,[],[f46,f94])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f386,plain,(
% 0.22/0.55    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f385,f65])).
% 0.22/0.55  fof(f385,plain,(
% 0.22/0.55    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f384,f64])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f383])).
% 0.22/0.55  fof(f383,plain,(
% 0.22/0.55    k2_struct_0(sK0) != k2_struct_0(sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f382,f278])).
% 0.22/0.55  fof(f382,plain,(
% 0.22/0.55    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f381,f65])).
% 0.22/0.55  fof(f381,plain,(
% 0.22/0.55    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f380,f64])).
% 0.22/0.55  fof(f380,plain,(
% 0.22/0.55    v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.55    inference(resolution,[],[f379,f175])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    v5_pre_topc(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f174,f70])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f173,f39])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f172,f36])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f171,f38])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f154,f71])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(backward_demodulation,[],[f135,f145])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f134,f64])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f133,f65])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f132,f64])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f131,f65])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f130,f64])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f129,f65])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f54,f42])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f379,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v5_pre_topc(k2_funct_1(sK2),X0,X1) | v3_tops_2(k2_funct_1(sK2),X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)),X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(resolution,[],[f211,f148])).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),X0,X1) | v3_tops_2(k2_funct_1(sK2),X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)),X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(resolution,[],[f210,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | v3_tops_2(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (31957)------------------------------
% 0.22/0.55  % (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31957)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (31957)Memory used [KB]: 1918
% 0.22/0.55  % (31957)Time elapsed: 0.109 s
% 0.22/0.55  % (31957)------------------------------
% 0.22/0.55  % (31957)------------------------------
% 0.22/0.55  % (31942)Success in time 0.183 s
%------------------------------------------------------------------------------
