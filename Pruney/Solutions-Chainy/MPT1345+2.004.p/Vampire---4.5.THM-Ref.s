%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  212 (12426 expanded)
%              Number of leaves         :   13 (4275 expanded)
%              Depth                    :   57
%              Number of atoms          : 1060 (78992 expanded)
%              Number of equality atoms :  161 (3122 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(resolution,[],[f347,f139])).

fof(f139,plain,(
    ~ v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f67,f138])).

fof(f138,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f137,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    & v3_tops_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f137,plain,
    ( ~ v1_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f136,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f65,f63])).

fof(f63,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f43,f61])).

fof(f61,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f40,f62])).

fof(f62,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f134,f69])).

fof(f69,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f64,f63])).

fof(f64,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f39,f62])).

fof(f39,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f134,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f89,f132])).

fof(f132,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f131,f38])).

fof(f131,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f130,f68])).

fof(f130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f129,f35])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f121,f37])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK1)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f117,f69])).

fof(f117,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f116,f62])).

fof(f116,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f115,f63])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f114,f62])).

fof(f114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f113,f63])).

fof(f113,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f112,f62])).

fof(f112,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f111,f63])).

fof(f111,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK2) != X1
      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

% (9431)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f88,plain,(
    v2_funct_1(sK2) ),
    inference(resolution,[],[f87,f38])).

fof(f87,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f86,f68])).

fof(f86,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f85,f35])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f84,f37])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f80,f69])).

fof(f80,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f79,f62])).

fof(f79,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f78,f63])).

fof(f78,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f77,f62])).

fof(f77,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f76,f63])).

fof(f76,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f66,f63])).

fof(f66,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f42,f62])).

fof(f42,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f347,plain,(
    v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f346,f38])).

fof(f346,plain,
    ( ~ v1_funct_1(sK2)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f345,f168])).

fof(f168,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f167,f38])).

fof(f167,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f165,f68])).

fof(f165,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f155,f69])).

fof(f155,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f58,f138])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f345,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f344,f35])).

fof(f344,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f343,f37])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK1)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f341,f159])).

fof(f159,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f158,f68])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f156,f69])).

fof(f156,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f57,f138])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f341,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f340])).

fof(f340,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f339,f108])).

fof(f108,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f100,f68])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f99,f35])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f98,f37])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f96,f69])).

fof(f96,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f95,f62])).

fof(f95,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f94,f63])).

fof(f94,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f93,f62])).

fof(f93,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f92,f63])).

fof(f92,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f41])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f339,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f338,f256])).

fof(f256,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f255,f141])).

fof(f141,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f73,f138])).

fof(f73,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f72,f69])).

fof(f72,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f71,f68])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,sK2)) ) ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f255,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f252,f38])).

fof(f252,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f251,f168])).

fof(f251,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f250,f159])).

fof(f250,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f204,f248])).

fof(f248,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f247,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f247,plain,
    ( v2_struct_0(sK1)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f245,f68])).

fof(f245,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f244,f61])).

fof(f244,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f243,f69])).

fof(f243,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f241,f132])).

fof(f241,plain,
    ( k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f240,f138])).

fof(f240,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f232,f63])).

fof(f232,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f231,f62])).

fof(f231,plain,(
    ! [X0] :
      ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f230,f62])).

fof(f230,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f229,f62])).

fof(f229,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f227,f62])).

fof(f227,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f189,f60])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f157,f38])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f46,f88])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f204,plain,(
    ! [X8,X9] :
      ( k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9
      | sK2 = k2_tops_2(X8,X9,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
      | ~ v1_funct_1(k2_funct_1(sK2)) ) ),
    inference(forward_demodulation,[],[f202,f97])).

fof(f97,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f68])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f90,f38])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (9424)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (9425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (9430)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (9436)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (9424)Refutation not found, incomplete strategy% (9424)------------------------------
% (9424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9424)Termination reason: Refutation not found, incomplete strategy

% (9424)Memory used [KB]: 6396
% (9424)Time elapsed: 0.118 s
% (9424)------------------------------
% (9424)------------------------------
% (9432)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (9439)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f202,plain,(
    ! [X8,X9] :
      ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2))
      | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
      | ~ v1_funct_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f197,f59])).

fof(f197,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f196,f68])).

fof(f196,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f195,f61])).

fof(f195,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f194,f69])).

fof(f194,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f192,f132])).

fof(f192,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f191,f138])).

fof(f191,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f184,f63])).

fof(f184,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f183,f62])).

fof(f183,plain,(
    ! [X0] :
      ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f182,f62])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f181,f62])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f179,f62])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f166,f60])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f135,f38])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f44,f88])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f338,plain,
    ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f337,f63])).

fof(f337,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f336,f62])).

fof(f336,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f335,f63])).

fof(f335,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f334,f62])).

fof(f334,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f333,f63])).

fof(f333,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f332,f62])).

fof(f332,plain,
    ( v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f331])).

fof(f331,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f330,f226])).

fof(f226,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f225,f36])).

fof(f225,plain,
    ( v2_struct_0(sK1)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f224,f68])).

fof(f224,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f223,f61])).

fof(f223,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f222,f69])).

fof(f222,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f221])).

fof(f221,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f220,f132])).

fof(f220,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f219,f138])).

fof(f219,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f213,f63])).

fof(f213,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f212,f62])).

fof(f212,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f211,f62])).

fof(f211,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f210,f62])).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(forward_demodulation,[],[f208,f62])).

fof(f208,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f173,f60])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) ) ),
    inference(resolution,[],[f152,f38])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f45,f88])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f330,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f329,f63])).

fof(f329,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f328,f62])).

fof(f328,plain,
    ( v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f327])).

fof(f327,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f326,f248])).

fof(f326,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f325,f63])).

fof(f325,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f324,f62])).

fof(f324,plain,
    ( v3_tops_2(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f308,f164])).

fof(f164,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f163,f68])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f162,f35])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f160,f37])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f145,f69])).

fof(f145,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(backward_demodulation,[],[f128,f138])).

fof(f128,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f127,f62])).

fof(f127,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f126,f63])).

fof(f126,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f125,f62])).

fof(f125,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f124,f63])).

fof(f124,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f123,f62])).

fof(f123,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f122,f63])).

fof(f122,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f308,plain,(
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
    inference(resolution,[],[f198,f141])).

fof(f198,plain,(
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
    inference(resolution,[],[f197,f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (9427)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (9419)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (9427)Refutation not found, incomplete strategy% (9427)------------------------------
% 0.22/0.49  % (9427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9427)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9427)Memory used [KB]: 10490
% 0.22/0.49  % (9427)Time elapsed: 0.062 s
% 0.22/0.49  % (9427)------------------------------
% 0.22/0.49  % (9427)------------------------------
% 0.22/0.49  % (9420)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.49  % (9420)Refutation not found, incomplete strategy% (9420)------------------------------
% 0.22/0.49  % (9420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9420)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9420)Memory used [KB]: 10618
% 0.22/0.49  % (9420)Time elapsed: 0.083 s
% 0.22/0.49  % (9420)------------------------------
% 0.22/0.49  % (9420)------------------------------
% 0.22/0.49  % (9421)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (9428)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (9426)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (9422)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (9417)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (9434)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (9438)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (9435)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (9429)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (9418)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (9437)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (9433)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (9426)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f348,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(resolution,[],[f347,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f67,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f137,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f31,f30,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),sK1,sK0) & v3_tops_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),sK1,sK0) & v3_tops_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f136,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.52    inference(backward_demodulation,[],[f65,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f43,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    l1_struct_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f47,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    l1_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    inference(backward_demodulation,[],[f40,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f43,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    l1_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f47,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f134,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f64,f63])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f39,f62])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(superposition,[],[f89,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f131,f38])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f130,f68])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f129,f35])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f121,f37])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f117,f69])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f116,f62])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f115,f63])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f114,f62])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f113,f63])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f112,f62])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f111,f63])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f49,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v3_tops_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f88,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  % (9431)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f87,f38])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | v2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f86,f68])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | v2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f85,f35])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f84,f37])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f80,f69])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f79,f62])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f78,f63])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f77,f62])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f76,f63])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f50,f41])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ~v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f66,f63])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ~v3_tops_2(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f42,f62])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f347,plain,(
% 0.22/0.52    v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f346,f38])).
% 0.22/0.52  fof(f346,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f345,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.52    inference(resolution,[],[f167,f38])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.52    inference(resolution,[],[f165,f68])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f155,f69])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(superposition,[],[f58,f138])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.52  fof(f345,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f344,f35])).
% 0.22/0.52  fof(f344,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f343,f37])).
% 0.22/0.52  fof(f343,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f342])).
% 0.22/0.52  fof(f342,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f341,f159])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f158,f68])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f156,f69])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(superposition,[],[f57,f138])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f341,plain,(
% 0.22/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f340])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f339,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f100,f68])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f99,f35])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f98,f37])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f96,f69])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f95,f62])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f94,f63])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f93,f62])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f92,f63])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f51,f41])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f339,plain,(
% 0.22/0.52    ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f338,f256])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f255,f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f73,f138])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.52    inference(resolution,[],[f72,f69])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.52    inference(resolution,[],[f71,f68])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_funct_1(k2_tops_2(X0,X1,sK2))) )),
% 0.22/0.52    inference(resolution,[],[f56,f38])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    ~v1_funct_1(k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f252,f38])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f251,f168])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f250,f159])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f249])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_struct_0(sK0) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(superposition,[],[f204,f248])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f247,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    v2_struct_0(sK1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f245,f68])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f244,f61])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    ~l1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f243,f69])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f242])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f241,f132])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f240,f138])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.52    inference(superposition,[],[f232,f63])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f231,f62])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    ( ! [X0] : (k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f230,f62])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f229,f62])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f227,f62])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.52    inference(resolution,[],[f189,f60])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)) )),
% 0.22/0.52    inference(resolution,[],[f157,f38])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_funct_1(sK2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f46,f88])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 | sK2 = k2_tops_2(X8,X9,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | ~v1_funct_1(k2_funct_1(sK2))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f202,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f91,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f55,f68])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f90,f38])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f88,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  % (9424)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (9425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (9430)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (9436)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (9424)Refutation not found, incomplete strategy% (9424)------------------------------
% 0.22/0.52  % (9424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9424)Memory used [KB]: 6396
% 0.22/0.52  % (9424)Time elapsed: 0.118 s
% 0.22/0.52  % (9424)------------------------------
% 0.22/0.52  % (9424)------------------------------
% 0.22/0.53  % (9432)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (9439)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    ( ! [X8,X9] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2)) | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | ~v1_funct_1(k2_funct_1(sK2))) )),
% 0.22/0.54    inference(resolution,[],[f197,f59])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f196,f68])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f195,f61])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    ~l1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f194,f69])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f193])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f192,f132])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f191,f138])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.22/0.54    inference(superposition,[],[f184,f63])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f183,f62])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    ( ! [X0] : (v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f182,f62])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f181,f62])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f179,f62])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(resolution,[],[f166,f60])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(resolution,[],[f135,f38])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(sK2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f44,f88])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f337,f63])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f336,f62])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f335,f63])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f334,f62])).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f333,f63])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f332,f62])).
% 0.22/0.54  fof(f332,plain,(
% 0.22/0.54    v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f331])).
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f330,f226])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f225,f36])).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    v2_struct_0(sK1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f224,f68])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f223,f61])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ~l1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f222,f69])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f221])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f220,f132])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f219,f138])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(superposition,[],[f213,f63])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f212,f62])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ( ! [X0] : (k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f211,f62])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f210,f62])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f208,f62])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(resolution,[],[f173,f60])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)) )),
% 0.22/0.54    inference(resolution,[],[f152,f38])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(sK2) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK2)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_struct_0(X1)) )),
% 0.22/0.54    inference(resolution,[],[f45,f88])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f329,f63])).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f328,f62])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f327])).
% 0.22/0.54  fof(f327,plain,(
% 0.22/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f326,f248])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f325,f63])).
% 0.22/0.54  fof(f325,plain,(
% 0.22/0.54    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f324,f62])).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    v3_tops_2(k2_funct_1(sK2),sK1,sK0) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f308,f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f163,f68])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f162,f35])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.54    inference(resolution,[],[f160,f37])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f145,f69])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(backward_demodulation,[],[f128,f138])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f127,f62])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f126,f63])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f125,f62])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f124,f63])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f123,f62])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f122,f63])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f52,f41])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v5_pre_topc(k2_funct_1(sK2),X0,X1) | v3_tops_2(k2_funct_1(sK2),X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)),X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(resolution,[],[f198,f141])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),X0,X1) | v3_tops_2(k2_funct_1(sK2),X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(sK2)),X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(resolution,[],[f197,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | v3_tops_2(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (9426)------------------------------
% 0.22/0.54  % (9426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9426)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (9426)Memory used [KB]: 1918
% 0.22/0.54  % (9426)Time elapsed: 0.106 s
% 0.22/0.54  % (9426)------------------------------
% 0.22/0.54  % (9426)------------------------------
% 0.22/0.54  % (9413)Success in time 0.18 s
%------------------------------------------------------------------------------
