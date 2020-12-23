%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:25 EST 2020

% Result     : Theorem 3.03s
% Output     : Refutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  193 (3991 expanded)
%              Number of leaves         :   27 (1398 expanded)
%              Depth                    :   34
%              Number of atoms          :  703 (27108 expanded)
%              Number of equality atoms :   83 ( 790 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4878,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4877,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f4877,plain,(
    ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f4861,f704])).

fof(f704,plain,(
    k1_xboole_0 = k2_pre_topc(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f703,f96])).

fof(f96,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v1_tdlat_3(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v1_tdlat_3(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v5_pre_topc(X2,sK1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ~ v5_pre_topc(X2,sK1,sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X2] :
        ( ~ v5_pre_topc(X2,sK1,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ~ v5_pre_topc(sK3,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

fof(f703,plain,
    ( k1_xboole_0 = k2_pre_topc(sK1,k1_xboole_0)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f699,f106])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f699,plain,
    ( k1_xboole_0 = k2_pre_topc(sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f662,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f662,plain,(
    v4_pre_topc(k1_xboole_0,sK1) ),
    inference(resolution,[],[f612,f106])).

fof(f612,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK1)))
      | v4_pre_topc(X11,sK1) ) ),
    inference(forward_demodulation,[],[f206,f341])).

fof(f341,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f182,f110])).

fof(f110,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f182,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f96,f112])).

fof(f112,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f206,plain,(
    ! [X11] :
      ( v4_pre_topc(X11,sK1)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f205,f94])).

fof(f94,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f205,plain,(
    ! [X11] :
      ( v4_pre_topc(X11,sK1)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f193,f95])).

fof(f95,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f193,plain,(
    ! [X11] :
      ( v4_pre_topc(X11,sK1)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_tdlat_3(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f96,f125])).

fof(f125,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK6(X0),X0)
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f4861,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f3197,f4693])).

fof(f4693,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f4676,f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f4676,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f4675,f103])).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4675,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f4673,f161])).

fof(f161,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4673,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f4654,f3073])).

fof(f3073,plain,(
    ! [X23,X22] :
      ( k1_relat_1(k1_xboole_0) = k1_relset_1(X22,X23,k1_xboole_0)
      | ~ v1_xboole_0(k2_zfmisc_1(X22,X23)) ) ),
    inference(forward_demodulation,[],[f1140,f1117])).

fof(f1117,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f1093,f111])).

fof(f1093,plain,(
    v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f1067,f103])).

fof(f1067,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3) ),
    inference(backward_demodulation,[],[f468,f1022])).

fof(f1022,plain,(
    k1_xboole_0 = k2_struct_0(sK2) ),
    inference(resolution,[],[f1012,f336])).

fof(f336,plain,
    ( sP0(sK1,sK3,sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f335,f96])).

fof(f335,plain,
    ( sP0(sK1,sK3,sK2)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f334,f98])).

fof(f98,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f334,plain,
    ( sP0(sK1,sK3,sK2)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f333,f99])).

fof(f99,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f333,plain,
    ( sP0(sK1,sK3,sK2)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f307,f100])).

fof(f100,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

fof(f307,plain,
    ( sP0(sK1,sK3,sK2)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f101,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f41,f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> ! [X3] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f101,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f1012,plain,(
    ~ sP0(sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f1011,f570])).

fof(f570,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(resolution,[],[f466,f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f466,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f348,f342])).

fof(f342,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f226,f110])).

fof(f226,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f98,f112])).

fof(f348,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f101,f341])).

fof(f1011,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ sP0(sK1,sK3,sK2) ),
    inference(forward_demodulation,[],[f1010,f341])).

fof(f1010,plain,
    ( ~ sP0(sK1,sK3,sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f1009,f94])).

fof(f1009,plain,
    ( ~ sP0(sK1,sK3,sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1008,f96])).

fof(f1008,plain,
    ( ~ sP0(sK1,sK3,sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1005,f95])).

fof(f1005,plain,
    ( ~ sP0(sK1,sK3,sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f988,f122])).

fof(f122,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
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
    inference(rectify,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f988,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | ~ sP0(sK1,sK3,sK2) ),
    inference(forward_demodulation,[],[f987,f341])).

fof(f987,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | ~ sP0(sK1,sK3,sK2) ),
    inference(forward_demodulation,[],[f268,f342])).

fof(f268,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | ~ sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f102,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X1,X0,X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0)
            & v3_pre_topc(sK4(X0,X1,X2),X2)
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0)
        & v3_pre_topc(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
              & v3_pre_topc(X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              & v3_pre_topc(X3,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ! [X3] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f102,plain,(
    ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f468,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(backward_demodulation,[],[f313,f342])).

fof(f313,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f101,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f1140,plain,(
    ! [X23,X22] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X22,X23))
      | k1_relat_1(sK3) = k1_relset_1(X22,X23,sK3) ) ),
    inference(resolution,[],[f1104,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1104,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f1092,f111])).

fof(f1092,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1065,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f1065,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f466,f1022])).

fof(f4654,plain,(
    ! [X0] : v1_xboole_0(k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f4653,f103])).

fof(f4653,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f4651,f161])).

fof(f4651,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relset_1(k1_xboole_0,X0,k1_xboole_0))
      | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f3535,f3680])).

fof(f3680,plain,(
    ! [X21,X20] :
      ( k1_relset_1(X20,X21,k1_xboole_0) = k8_relset_1(X20,X21,k1_xboole_0,X21)
      | ~ v1_xboole_0(k2_zfmisc_1(X20,X21)) ) ),
    inference(forward_demodulation,[],[f1139,f1117])).

fof(f1139,plain,(
    ! [X21,X20] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X20,X21))
      | k1_relset_1(X20,X21,sK3) = k8_relset_1(X20,X21,sK3,X21) ) ),
    inference(resolution,[],[f1104,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f3535,plain,(
    ! [X17,X16] : v1_xboole_0(k8_relset_1(k1_xboole_0,X16,k1_xboole_0,X17)) ),
    inference(subsumption_resolution,[],[f3534,f103])).

fof(f3534,plain,(
    ! [X17,X16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k8_relset_1(k1_xboole_0,X16,k1_xboole_0,X17)) ) ),
    inference(forward_demodulation,[],[f3498,f161])).

fof(f3498,plain,(
    ! [X17,X16] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X16))
      | v1_xboole_0(k8_relset_1(k1_xboole_0,X16,k1_xboole_0,X17)) ) ),
    inference(resolution,[],[f3447,f2523])).

fof(f2523,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X2) ) ),
    inference(forward_demodulation,[],[f2522,f160])).

fof(f2522,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k1_xboole_0)))
      | v1_xboole_0(X2) ) ),
    inference(forward_demodulation,[],[f1115,f1117])).

fof(f1115,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) ) ),
    inference(resolution,[],[f1093,f134])).

fof(f3447,plain,(
    ! [X17,X15,X16] :
      ( m1_subset_1(k8_relset_1(X15,X16,k1_xboole_0,X17),k1_zfmisc_1(X15))
      | ~ v1_xboole_0(k2_zfmisc_1(X15,X16)) ) ),
    inference(forward_demodulation,[],[f1137,f1117])).

fof(f1137,plain,(
    ! [X17,X15,X16] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X15,X16))
      | m1_subset_1(k8_relset_1(X15,X16,sK3,X17),k1_zfmisc_1(X15)) ) ),
    inference(resolution,[],[f1104,f156])).

fof(f3197,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k1_relat_1(k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f3182,f1327])).

fof(f1327,plain,(
    k1_relat_1(k1_xboole_0) = k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1087,f1117])).

fof(f1087,plain,(
    k1_relat_1(sK3) = k8_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f946,f1022])).

fof(f946,plain,(
    k1_relat_1(sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f945,f573])).

fof(f573,plain,(
    k1_relat_1(sK3) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(resolution,[],[f466,f151])).

fof(f945,plain,(
    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f944,f341])).

fof(f944,plain,(
    k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3) = k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f311,f342])).

fof(f311,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f101,f153])).

fof(f3182,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1605,f2415])).

fof(f2415,plain,(
    k1_xboole_0 = sK7(sK1,sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2410,f104])).

fof(f2410,plain,
    ( k1_xboole_0 = sK7(sK1,sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK7(sK1,sK2,k1_xboole_0)) ),
    inference(resolution,[],[f1271,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1271,plain,(
    r1_tarski(sK7(sK1,sK2,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f1264,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1264,plain,(
    m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1076,f1117])).

fof(f1076,plain,(
    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f621,f1022])).

fof(f621,plain,(
    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f325,f342])).

fof(f325,plain,(
    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f324,f94])).

fof(f324,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f323,f96])).

fof(f323,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f322,f97])).

fof(f97,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f322,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f321,f98])).

fof(f321,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f320,f99])).

fof(f320,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f319,f100])).

fof(f319,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f305,f102])).

fof(f305,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f101,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f79,f80])).

fof(f80,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(f1605,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK7(sK1,sK2,k1_xboole_0))),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(sK1,sK2,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f1089,f1117])).

fof(f1089,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3,sK7(sK1,sK2,sK3))),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) ),
    inference(backward_demodulation,[],[f1021,f1022])).

fof(f1021,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) ),
    inference(forward_demodulation,[],[f1020,f341])).

fof(f1020,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) ),
    inference(forward_demodulation,[],[f332,f342])).

fof(f332,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) ),
    inference(subsumption_resolution,[],[f331,f94])).

fof(f331,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f330,f96])).

fof(f330,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f329,f97])).

fof(f329,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f328,f98])).

fof(f328,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f327,f99])).

fof(f327,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f326,f100])).

fof(f326,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f306,f102])).

fof(f306,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f101,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (28072)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (28083)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (28081)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (28085)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (28078)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (28070)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (28075)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (28088)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (28082)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (28068)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (28076)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (28066)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (28066)Refutation not found, incomplete strategy% (28066)------------------------------
% 0.21/0.50  % (28066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28066)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28066)Memory used [KB]: 10490
% 0.21/0.50  % (28066)Time elapsed: 0.004 s
% 0.21/0.50  % (28066)------------------------------
% 0.21/0.50  % (28066)------------------------------
% 0.21/0.50  % (28072)Refutation not found, incomplete strategy% (28072)------------------------------
% 0.21/0.50  % (28072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28072)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28072)Memory used [KB]: 10746
% 0.21/0.50  % (28072)Time elapsed: 0.087 s
% 0.21/0.50  % (28072)------------------------------
% 0.21/0.50  % (28072)------------------------------
% 0.21/0.50  % (28071)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (28086)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (28079)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (28089)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (28079)Refutation not found, incomplete strategy% (28079)------------------------------
% 0.21/0.51  % (28079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28079)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28079)Memory used [KB]: 6140
% 0.21/0.51  % (28079)Time elapsed: 0.098 s
% 0.21/0.51  % (28079)------------------------------
% 0.21/0.51  % (28079)------------------------------
% 0.21/0.51  % (28080)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (28067)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (28069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (28084)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (28090)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (28077)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (28077)Refutation not found, incomplete strategy% (28077)------------------------------
% 0.21/0.53  % (28077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28077)Memory used [KB]: 10490
% 0.21/0.53  % (28077)Time elapsed: 0.002 s
% 0.21/0.53  % (28077)------------------------------
% 0.21/0.53  % (28077)------------------------------
% 0.21/0.53  % (28087)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (28074)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.41/0.54  % (28091)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.54  % (28071)Refutation not found, incomplete strategy% (28071)------------------------------
% 1.41/0.54  % (28071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (28071)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (28071)Memory used [KB]: 6652
% 1.41/0.54  % (28071)Time elapsed: 0.109 s
% 1.41/0.54  % (28071)------------------------------
% 1.41/0.54  % (28071)------------------------------
% 1.41/0.54  % (28073)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.55/0.61  % (28075)Refutation not found, incomplete strategy% (28075)------------------------------
% 1.55/0.61  % (28075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (28075)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (28075)Memory used [KB]: 6140
% 1.55/0.61  % (28075)Time elapsed: 0.166 s
% 1.55/0.61  % (28075)------------------------------
% 1.55/0.61  % (28075)------------------------------
% 3.03/0.75  % (28084)Refutation found. Thanks to Tanya!
% 3.03/0.75  % SZS status Theorem for theBenchmark
% 3.03/0.75  % SZS output start Proof for theBenchmark
% 3.03/0.75  fof(f4878,plain,(
% 3.03/0.75    $false),
% 3.03/0.75    inference(subsumption_resolution,[],[f4877,f104])).
% 3.03/0.75  fof(f104,plain,(
% 3.03/0.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f5])).
% 3.03/0.75  fof(f5,axiom,(
% 3.03/0.75    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.03/0.75  fof(f4877,plain,(
% 3.03/0.75    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 3.03/0.75    inference(forward_demodulation,[],[f4861,f704])).
% 3.03/0.75  fof(f704,plain,(
% 3.03/0.75    k1_xboole_0 = k2_pre_topc(sK1,k1_xboole_0)),
% 3.03/0.75    inference(subsumption_resolution,[],[f703,f96])).
% 3.03/0.75  fof(f96,plain,(
% 3.03/0.75    l1_pre_topc(sK1)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f65,plain,(
% 3.03/0.75    ((~v5_pre_topc(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1)),
% 3.03/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f64,f63,f62])).
% 3.03/0.75  fof(f62,plain,(
% 3.03/0.75    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f63,plain,(
% 3.03/0.75    ? [X1] : (? [X2] : (~v5_pre_topc(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,sK1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f64,plain,(
% 3.03/0.75    ? [X2] : (~v5_pre_topc(X2,sK1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => (~v5_pre_topc(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f34,plain,(
% 3.03/0.75    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 3.03/0.75    inference(flattening,[],[f33])).
% 3.03/0.75  fof(f33,plain,(
% 3.03/0.75    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 3.03/0.75    inference(ennf_transformation,[],[f31])).
% 3.03/0.75  fof(f31,negated_conjecture,(
% 3.03/0.75    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 3.03/0.75    inference(negated_conjecture,[],[f30])).
% 3.03/0.75  fof(f30,conjecture,(
% 3.03/0.75    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).
% 3.03/0.75  fof(f703,plain,(
% 3.03/0.75    k1_xboole_0 = k2_pre_topc(sK1,k1_xboole_0) | ~l1_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f699,f106])).
% 3.03/0.75  fof(f106,plain,(
% 3.03/0.75    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.03/0.75    inference(cnf_transformation,[],[f10])).
% 3.03/0.75  fof(f10,axiom,(
% 3.03/0.75    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.03/0.75  fof(f699,plain,(
% 3.03/0.75    k1_xboole_0 = k2_pre_topc(sK1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 3.03/0.75    inference(resolution,[],[f662,f120])).
% 3.03/0.75  fof(f120,plain,(
% 3.03/0.75    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f43])).
% 3.03/0.75  fof(f43,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.75    inference(flattening,[],[f42])).
% 3.03/0.75  fof(f42,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.75    inference(ennf_transformation,[],[f24])).
% 3.03/0.75  fof(f24,axiom,(
% 3.03/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 3.03/0.75  fof(f662,plain,(
% 3.03/0.75    v4_pre_topc(k1_xboole_0,sK1)),
% 3.03/0.75    inference(resolution,[],[f612,f106])).
% 3.03/0.75  fof(f612,plain,(
% 3.03/0.75    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK1))) | v4_pre_topc(X11,sK1)) )),
% 3.03/0.75    inference(forward_demodulation,[],[f206,f341])).
% 3.03/0.75  fof(f341,plain,(
% 3.03/0.75    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 3.03/0.75    inference(resolution,[],[f182,f110])).
% 3.03/0.75  fof(f110,plain,(
% 3.03/0.75    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f35])).
% 3.03/0.75  fof(f35,plain,(
% 3.03/0.75    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.03/0.75    inference(ennf_transformation,[],[f22])).
% 3.03/0.75  fof(f22,axiom,(
% 3.03/0.75    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 3.03/0.75  fof(f182,plain,(
% 3.03/0.75    l1_struct_0(sK1)),
% 3.03/0.75    inference(resolution,[],[f96,f112])).
% 3.03/0.75  fof(f112,plain,(
% 3.03/0.75    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f37])).
% 3.03/0.75  fof(f37,plain,(
% 3.03/0.75    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.03/0.75    inference(ennf_transformation,[],[f23])).
% 3.03/0.75  fof(f23,axiom,(
% 3.03/0.75    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.03/0.75  fof(f206,plain,(
% 3.03/0.75    ( ! [X11] : (v4_pre_topc(X11,sK1) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 3.03/0.75    inference(subsumption_resolution,[],[f205,f94])).
% 3.03/0.75  fof(f94,plain,(
% 3.03/0.75    v2_pre_topc(sK1)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f205,plain,(
% 3.03/0.75    ( ! [X11] : (v4_pre_topc(X11,sK1) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)) )),
% 3.03/0.75    inference(subsumption_resolution,[],[f193,f95])).
% 3.03/0.75  fof(f95,plain,(
% 3.03/0.75    v1_tdlat_3(sK1)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f193,plain,(
% 3.03/0.75    ( ! [X11] : (v4_pre_topc(X11,sK1) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_tdlat_3(sK1) | ~v2_pre_topc(sK1)) )),
% 3.03/0.75    inference(resolution,[],[f96,f125])).
% 3.03/0.75  fof(f125,plain,(
% 3.03/0.75    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f77])).
% 3.03/0.75  fof(f77,plain,(
% 3.03/0.75    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).
% 3.03/0.75  fof(f76,plain,(
% 3.03/0.75    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f75,plain,(
% 3.03/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(rectify,[],[f74])).
% 3.03/0.75  fof(f74,plain,(
% 3.03/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(nnf_transformation,[],[f47])).
% 3.03/0.75  fof(f47,plain,(
% 3.03/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(flattening,[],[f46])).
% 3.03/0.75  fof(f46,plain,(
% 3.03/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/0.75    inference(ennf_transformation,[],[f29])).
% 3.03/0.75  fof(f29,axiom,(
% 3.03/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).
% 3.03/0.75  fof(f4861,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 3.03/0.75    inference(backward_demodulation,[],[f3197,f4693])).
% 3.03/0.75  fof(f4693,plain,(
% 3.03/0.75    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.03/0.75    inference(resolution,[],[f4676,f111])).
% 3.03/0.75  fof(f111,plain,(
% 3.03/0.75    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f36])).
% 3.03/0.75  fof(f36,plain,(
% 3.03/0.75    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.03/0.75    inference(ennf_transformation,[],[f3])).
% 3.03/0.75  fof(f3,axiom,(
% 3.03/0.75    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.03/0.75  fof(f4676,plain,(
% 3.03/0.75    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 3.03/0.75    inference(subsumption_resolution,[],[f4675,f103])).
% 3.03/0.75  fof(f103,plain,(
% 3.03/0.75    v1_xboole_0(k1_xboole_0)),
% 3.03/0.75    inference(cnf_transformation,[],[f2])).
% 3.03/0.75  fof(f2,axiom,(
% 3.03/0.75    v1_xboole_0(k1_xboole_0)),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.03/0.75  fof(f4675,plain,(
% 3.03/0.75    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 3.03/0.75    inference(forward_demodulation,[],[f4673,f161])).
% 3.03/0.75  fof(f161,plain,(
% 3.03/0.75    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.03/0.75    inference(equality_resolution,[],[f143])).
% 3.03/0.75  fof(f143,plain,(
% 3.03/0.75    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.03/0.75    inference(cnf_transformation,[],[f91])).
% 3.03/0.75  fof(f91,plain,(
% 3.03/0.75    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.03/0.75    inference(flattening,[],[f90])).
% 3.03/0.75  fof(f90,plain,(
% 3.03/0.75    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.03/0.75    inference(nnf_transformation,[],[f7])).
% 3.03/0.75  fof(f7,axiom,(
% 3.03/0.75    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.03/0.75  fof(f4673,plain,(
% 3.03/0.75    ( ! [X0] : (v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 3.03/0.75    inference(superposition,[],[f4654,f3073])).
% 3.03/0.75  fof(f3073,plain,(
% 3.03/0.75    ( ! [X23,X22] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X22,X23,k1_xboole_0) | ~v1_xboole_0(k2_zfmisc_1(X22,X23))) )),
% 3.03/0.75    inference(forward_demodulation,[],[f1140,f1117])).
% 3.03/0.75  fof(f1117,plain,(
% 3.03/0.75    k1_xboole_0 = sK3),
% 3.03/0.75    inference(resolution,[],[f1093,f111])).
% 3.03/0.75  fof(f1093,plain,(
% 3.03/0.75    v1_xboole_0(sK3)),
% 3.03/0.75    inference(subsumption_resolution,[],[f1067,f103])).
% 3.03/0.75  fof(f1067,plain,(
% 3.03/0.75    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3)),
% 3.03/0.75    inference(backward_demodulation,[],[f468,f1022])).
% 3.03/0.75  fof(f1022,plain,(
% 3.03/0.75    k1_xboole_0 = k2_struct_0(sK2)),
% 3.03/0.75    inference(resolution,[],[f1012,f336])).
% 3.03/0.75  fof(f336,plain,(
% 3.03/0.75    sP0(sK1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 3.03/0.75    inference(subsumption_resolution,[],[f335,f96])).
% 3.03/0.75  fof(f335,plain,(
% 3.03/0.75    sP0(sK1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~l1_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f334,f98])).
% 3.03/0.75  fof(f98,plain,(
% 3.03/0.75    l1_pre_topc(sK2)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f334,plain,(
% 3.03/0.75    sP0(sK1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f333,f99])).
% 3.03/0.75  fof(f99,plain,(
% 3.03/0.75    v1_funct_1(sK3)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f333,plain,(
% 3.03/0.75    sP0(sK1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f307,f100])).
% 3.03/0.75  fof(f100,plain,(
% 3.03/0.75    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f307,plain,(
% 3.03/0.75    sP0(sK1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 3.03/0.75    inference(resolution,[],[f101,f118])).
% 3.03/0.75  fof(f118,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f61])).
% 3.03/0.75  fof(f61,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : (sP0(X0,X2,X1) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.03/0.75    inference(definition_folding,[],[f41,f60])).
% 3.03/0.75  fof(f60,plain,(
% 3.03/0.75    ! [X0,X2,X1] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~sP0(X0,X2,X1))),
% 3.03/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.03/0.75  fof(f41,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.03/0.75    inference(flattening,[],[f40])).
% 3.03/0.75  fof(f40,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.03/0.75    inference(ennf_transformation,[],[f25])).
% 3.03/0.75  fof(f25,axiom,(
% 3.03/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 3.03/0.75  fof(f101,plain,(
% 3.03/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f1012,plain,(
% 3.03/0.75    ~sP0(sK1,sK3,sK2)),
% 3.03/0.75    inference(subsumption_resolution,[],[f1011,f570])).
% 3.03/0.75  fof(f570,plain,(
% 3.03/0.75    ( ! [X0] : (m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0),k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 3.03/0.75    inference(resolution,[],[f466,f156])).
% 3.03/0.75  fof(f156,plain,(
% 3.03/0.75    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.75    inference(cnf_transformation,[],[f59])).
% 3.03/0.75  fof(f59,plain,(
% 3.03/0.75    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.75    inference(ennf_transformation,[],[f16])).
% 3.03/0.75  fof(f16,axiom,(
% 3.03/0.75    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 3.03/0.75  fof(f466,plain,(
% 3.03/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 3.03/0.75    inference(backward_demodulation,[],[f348,f342])).
% 3.03/0.75  fof(f342,plain,(
% 3.03/0.75    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 3.03/0.75    inference(resolution,[],[f226,f110])).
% 3.03/0.75  fof(f226,plain,(
% 3.03/0.75    l1_struct_0(sK2)),
% 3.03/0.75    inference(resolution,[],[f98,f112])).
% 3.03/0.75  fof(f348,plain,(
% 3.03/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 3.03/0.75    inference(backward_demodulation,[],[f101,f341])).
% 3.03/0.75  fof(f1011,plain,(
% 3.03/0.75    ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1))) | ~sP0(sK1,sK3,sK2)),
% 3.03/0.75    inference(forward_demodulation,[],[f1010,f341])).
% 3.03/0.75  fof(f1010,plain,(
% 3.03/0.75    ~sP0(sK1,sK3,sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.03/0.75    inference(subsumption_resolution,[],[f1009,f94])).
% 3.03/0.75  fof(f1009,plain,(
% 3.03/0.75    ~sP0(sK1,sK3,sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f1008,f96])).
% 3.03/0.75  fof(f1008,plain,(
% 3.03/0.75    ~sP0(sK1,sK3,sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f1005,f95])).
% 3.03/0.75  fof(f1005,plain,(
% 3.03/0.75    ~sP0(sK1,sK3,sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(resolution,[],[f988,f122])).
% 3.03/0.75  fof(f122,plain,(
% 3.03/0.75    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f73])).
% 3.03/0.75  fof(f73,plain,(
% 3.03/0.75    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).
% 3.03/0.75  fof(f72,plain,(
% 3.03/0.75    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f71,plain,(
% 3.03/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(rectify,[],[f70])).
% 3.03/0.75  fof(f70,plain,(
% 3.03/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(nnf_transformation,[],[f45])).
% 3.03/0.75  fof(f45,plain,(
% 3.03/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(flattening,[],[f44])).
% 3.03/0.75  fof(f44,plain,(
% 3.03/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/0.75    inference(ennf_transformation,[],[f28])).
% 3.03/0.75  fof(f28,axiom,(
% 3.03/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 3.03/0.75  fof(f988,plain,(
% 3.03/0.75    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | ~sP0(sK1,sK3,sK2)),
% 3.03/0.75    inference(forward_demodulation,[],[f987,f341])).
% 3.03/0.75  fof(f987,plain,(
% 3.03/0.75    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | ~sP0(sK1,sK3,sK2)),
% 3.03/0.75    inference(forward_demodulation,[],[f268,f342])).
% 3.03/0.75  fof(f268,plain,(
% 3.03/0.75    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | ~sP0(sK1,sK3,sK2)),
% 3.03/0.75    inference(resolution,[],[f102,f117])).
% 3.03/0.75  fof(f117,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (v5_pre_topc(X1,X0,X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0) | ~sP0(X0,X1,X2)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f69])).
% 3.03/0.75  fof(f69,plain,(
% 3.03/0.75    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 3.03/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).
% 3.03/0.75  fof(f68,plain,(
% 3.03/0.75    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f67,plain,(
% 3.03/0.75    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 3.03/0.75    inference(rectify,[],[f66])).
% 3.03/0.75  fof(f66,plain,(
% 3.03/0.75    ! [X0,X2,X1] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~sP0(X0,X2,X1))),
% 3.03/0.75    inference(nnf_transformation,[],[f60])).
% 3.03/0.75  fof(f102,plain,(
% 3.03/0.75    ~v5_pre_topc(sK3,sK1,sK2)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f468,plain,(
% 3.03/0.75    ~v1_xboole_0(k2_struct_0(sK2)) | v1_xboole_0(sK3)),
% 3.03/0.75    inference(backward_demodulation,[],[f313,f342])).
% 3.03/0.75  fof(f313,plain,(
% 3.03/0.75    ~v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(sK3)),
% 3.03/0.75    inference(resolution,[],[f101,f134])).
% 3.03/0.75  fof(f134,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f50])).
% 3.03/0.75  fof(f50,plain,(
% 3.03/0.75    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.03/0.75    inference(ennf_transformation,[],[f15])).
% 3.03/0.75  fof(f15,axiom,(
% 3.03/0.75    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 3.03/0.75  fof(f1140,plain,(
% 3.03/0.75    ( ! [X23,X22] : (~v1_xboole_0(k2_zfmisc_1(X22,X23)) | k1_relat_1(sK3) = k1_relset_1(X22,X23,sK3)) )),
% 3.03/0.75    inference(resolution,[],[f1104,f151])).
% 3.03/0.75  fof(f151,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.75    inference(cnf_transformation,[],[f54])).
% 3.03/0.75  fof(f54,plain,(
% 3.03/0.75    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.75    inference(ennf_transformation,[],[f17])).
% 3.03/0.75  fof(f17,axiom,(
% 3.03/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.03/0.75  fof(f1104,plain,(
% 3.03/0.75    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.03/0.75    inference(superposition,[],[f1092,f111])).
% 3.03/0.75  fof(f1092,plain,(
% 3.03/0.75    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 3.03/0.75    inference(forward_demodulation,[],[f1065,f160])).
% 3.03/0.75  fof(f160,plain,(
% 3.03/0.75    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.03/0.75    inference(equality_resolution,[],[f144])).
% 3.03/0.75  fof(f144,plain,(
% 3.03/0.75    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.03/0.75    inference(cnf_transformation,[],[f91])).
% 3.03/0.75  fof(f1065,plain,(
% 3.03/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)))),
% 3.03/0.75    inference(backward_demodulation,[],[f466,f1022])).
% 3.03/0.75  fof(f4654,plain,(
% 3.03/0.75    ( ! [X0] : (v1_xboole_0(k1_relset_1(k1_xboole_0,X0,k1_xboole_0))) )),
% 3.03/0.75    inference(subsumption_resolution,[],[f4653,f103])).
% 3.03/0.75  fof(f4653,plain,(
% 3.03/0.75    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_relset_1(k1_xboole_0,X0,k1_xboole_0))) )),
% 3.03/0.75    inference(forward_demodulation,[],[f4651,f161])).
% 3.03/0.75  fof(f4651,plain,(
% 3.03/0.75    ( ! [X0] : (v1_xboole_0(k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) | ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 3.03/0.75    inference(superposition,[],[f3535,f3680])).
% 3.03/0.75  fof(f3680,plain,(
% 3.03/0.75    ( ! [X21,X20] : (k1_relset_1(X20,X21,k1_xboole_0) = k8_relset_1(X20,X21,k1_xboole_0,X21) | ~v1_xboole_0(k2_zfmisc_1(X20,X21))) )),
% 3.03/0.75    inference(forward_demodulation,[],[f1139,f1117])).
% 3.03/0.75  fof(f1139,plain,(
% 3.03/0.75    ( ! [X21,X20] : (~v1_xboole_0(k2_zfmisc_1(X20,X21)) | k1_relset_1(X20,X21,sK3) = k8_relset_1(X20,X21,sK3,X21)) )),
% 3.03/0.75    inference(resolution,[],[f1104,f153])).
% 3.03/0.75  fof(f153,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.75    inference(cnf_transformation,[],[f55])).
% 3.03/0.75  fof(f55,plain,(
% 3.03/0.75    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.75    inference(ennf_transformation,[],[f18])).
% 3.03/0.75  fof(f18,axiom,(
% 3.03/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 3.03/0.75  fof(f3535,plain,(
% 3.03/0.75    ( ! [X17,X16] : (v1_xboole_0(k8_relset_1(k1_xboole_0,X16,k1_xboole_0,X17))) )),
% 3.03/0.75    inference(subsumption_resolution,[],[f3534,f103])).
% 3.03/0.75  fof(f3534,plain,(
% 3.03/0.75    ( ! [X17,X16] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k8_relset_1(k1_xboole_0,X16,k1_xboole_0,X17))) )),
% 3.03/0.75    inference(forward_demodulation,[],[f3498,f161])).
% 3.03/0.75  fof(f3498,plain,(
% 3.03/0.75    ( ! [X17,X16] : (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X16)) | v1_xboole_0(k8_relset_1(k1_xboole_0,X16,k1_xboole_0,X17))) )),
% 3.03/0.75    inference(resolution,[],[f3447,f2523])).
% 3.03/0.75  fof(f2523,plain,(
% 3.03/0.75    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X2)) )),
% 3.03/0.75    inference(forward_demodulation,[],[f2522,f160])).
% 3.03/0.75  fof(f2522,plain,(
% 3.03/0.75    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k1_xboole_0))) | v1_xboole_0(X2)) )),
% 3.03/0.75    inference(forward_demodulation,[],[f1115,f1117])).
% 3.03/0.75  fof(f1115,plain,(
% 3.03/0.75    ( ! [X2,X3] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,sK3)))) )),
% 3.03/0.75    inference(resolution,[],[f1093,f134])).
% 3.03/0.75  fof(f3447,plain,(
% 3.03/0.75    ( ! [X17,X15,X16] : (m1_subset_1(k8_relset_1(X15,X16,k1_xboole_0,X17),k1_zfmisc_1(X15)) | ~v1_xboole_0(k2_zfmisc_1(X15,X16))) )),
% 3.03/0.75    inference(forward_demodulation,[],[f1137,f1117])).
% 3.03/0.75  fof(f1137,plain,(
% 3.03/0.75    ( ! [X17,X15,X16] : (~v1_xboole_0(k2_zfmisc_1(X15,X16)) | m1_subset_1(k8_relset_1(X15,X16,sK3,X17),k1_zfmisc_1(X15))) )),
% 3.03/0.75    inference(resolution,[],[f1104,f156])).
% 3.03/0.75  fof(f3197,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k1_relat_1(k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 3.03/0.75    inference(forward_demodulation,[],[f3182,f1327])).
% 3.03/0.75  fof(f1327,plain,(
% 3.03/0.75    k1_relat_1(k1_xboole_0) = k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 3.03/0.75    inference(forward_demodulation,[],[f1087,f1117])).
% 3.03/0.75  fof(f1087,plain,(
% 3.03/0.75    k1_relat_1(sK3) = k8_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3,k1_xboole_0)),
% 3.03/0.75    inference(backward_demodulation,[],[f946,f1022])).
% 3.03/0.75  fof(f946,plain,(
% 3.03/0.75    k1_relat_1(sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2))),
% 3.03/0.75    inference(forward_demodulation,[],[f945,f573])).
% 3.03/0.75  fof(f573,plain,(
% 3.03/0.75    k1_relat_1(sK3) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 3.03/0.75    inference(resolution,[],[f466,f151])).
% 3.03/0.75  fof(f945,plain,(
% 3.03/0.75    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2))),
% 3.03/0.75    inference(forward_demodulation,[],[f944,f341])).
% 3.03/0.75  fof(f944,plain,(
% 3.03/0.75    k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3) = k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2))),
% 3.03/0.75    inference(forward_demodulation,[],[f311,f342])).
% 3.03/0.75  fof(f311,plain,(
% 3.03/0.75    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,u1_struct_0(sK2))),
% 3.03/0.75    inference(resolution,[],[f101,f153])).
% 3.03/0.75  fof(f3182,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 3.03/0.75    inference(backward_demodulation,[],[f1605,f2415])).
% 3.03/0.75  fof(f2415,plain,(
% 3.03/0.75    k1_xboole_0 = sK7(sK1,sK2,k1_xboole_0)),
% 3.03/0.75    inference(subsumption_resolution,[],[f2410,f104])).
% 3.03/0.75  fof(f2410,plain,(
% 3.03/0.75    k1_xboole_0 = sK7(sK1,sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK7(sK1,sK2,k1_xboole_0))),
% 3.03/0.75    inference(resolution,[],[f1271,f139])).
% 3.03/0.75  fof(f139,plain,(
% 3.03/0.75    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f88])).
% 3.03/0.75  fof(f88,plain,(
% 3.03/0.75    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.75    inference(flattening,[],[f87])).
% 3.03/0.75  fof(f87,plain,(
% 3.03/0.75    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.75    inference(nnf_transformation,[],[f4])).
% 3.03/0.75  fof(f4,axiom,(
% 3.03/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.03/0.75  fof(f1271,plain,(
% 3.03/0.75    r1_tarski(sK7(sK1,sK2,k1_xboole_0),k1_xboole_0)),
% 3.03/0.75    inference(resolution,[],[f1264,f140])).
% 3.03/0.75  fof(f140,plain,(
% 3.03/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.03/0.75    inference(cnf_transformation,[],[f89])).
% 3.03/0.75  fof(f89,plain,(
% 3.03/0.75    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.03/0.75    inference(nnf_transformation,[],[f11])).
% 3.03/0.75  fof(f11,axiom,(
% 3.03/0.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.03/0.75  fof(f1264,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 3.03/0.75    inference(forward_demodulation,[],[f1076,f1117])).
% 3.03/0.75  fof(f1076,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(k1_xboole_0))),
% 3.03/0.75    inference(backward_demodulation,[],[f621,f1022])).
% 3.03/0.75  fof(f621,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))),
% 3.03/0.75    inference(forward_demodulation,[],[f325,f342])).
% 3.03/0.75  fof(f325,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.03/0.75    inference(subsumption_resolution,[],[f324,f94])).
% 3.03/0.75  fof(f324,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f323,f96])).
% 3.03/0.75  fof(f323,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f322,f97])).
% 3.03/0.75  fof(f97,plain,(
% 3.03/0.75    v2_pre_topc(sK2)),
% 3.03/0.75    inference(cnf_transformation,[],[f65])).
% 3.03/0.75  fof(f322,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f321,f98])).
% 3.03/0.75  fof(f321,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f320,f99])).
% 3.03/0.75  fof(f320,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f319,f100])).
% 3.03/0.75  fof(f319,plain,(
% 3.03/0.75    m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f305,f102])).
% 3.03/0.75  fof(f305,plain,(
% 3.03/0.75    v5_pre_topc(sK3,sK1,sK2) | m1_subset_1(sK7(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(resolution,[],[f101,f129])).
% 3.03/0.75  fof(f129,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f81])).
% 3.03/0.75  fof(f81,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f79,f80])).
% 3.03/0.75  fof(f80,plain,(
% 3.03/0.75    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.03/0.75    introduced(choice_axiom,[])).
% 3.03/0.75  fof(f79,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(rectify,[],[f78])).
% 3.03/0.75  fof(f78,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(nnf_transformation,[],[f49])).
% 3.03/0.75  fof(f49,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.75    inference(flattening,[],[f48])).
% 3.03/0.75  fof(f48,plain,(
% 3.03/0.75    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/0.75    inference(ennf_transformation,[],[f26])).
% 3.03/0.75  fof(f26,axiom,(
% 3.03/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 3.03/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).
% 3.03/0.75  fof(f1605,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK7(sK1,sK2,k1_xboole_0))),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(sK1,sK2,k1_xboole_0))))),
% 3.03/0.75    inference(forward_demodulation,[],[f1089,f1117])).
% 3.03/0.75  fof(f1089,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3,sK7(sK1,sK2,sK3))),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))),
% 3.03/0.75    inference(backward_demodulation,[],[f1021,f1022])).
% 3.03/0.75  fof(f1021,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))),
% 3.03/0.75    inference(forward_demodulation,[],[f1020,f341])).
% 3.03/0.75  fof(f1020,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))),
% 3.03/0.75    inference(forward_demodulation,[],[f332,f342])).
% 3.03/0.75  fof(f332,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3))))),
% 3.03/0.75    inference(subsumption_resolution,[],[f331,f94])).
% 3.03/0.75  fof(f331,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f330,f96])).
% 3.03/0.75  fof(f330,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f329,f97])).
% 3.03/0.75  fof(f329,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f328,f98])).
% 3.03/0.75  fof(f328,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f327,f99])).
% 3.03/0.75  fof(f327,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f326,f100])).
% 3.03/0.75  fof(f326,plain,(
% 3.03/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(subsumption_resolution,[],[f306,f102])).
% 3.03/0.75  fof(f306,plain,(
% 3.03/0.75    v5_pre_topc(sK3,sK1,sK2) | ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK7(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(sK1,sK2,sK3)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.03/0.75    inference(resolution,[],[f101,f130])).
% 3.03/0.75  fof(f130,plain,(
% 3.03/0.75    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f81])).
% 3.03/0.75  % SZS output end Proof for theBenchmark
% 3.03/0.75  % (28084)------------------------------
% 3.03/0.75  % (28084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.75  % (28084)Termination reason: Refutation
% 3.03/0.75  
% 3.03/0.75  % (28084)Memory used [KB]: 3582
% 3.03/0.75  % (28084)Time elapsed: 0.335 s
% 3.03/0.75  % (28084)------------------------------
% 3.03/0.75  % (28084)------------------------------
% 3.03/0.75  % (28065)Success in time 0.392 s
%------------------------------------------------------------------------------
