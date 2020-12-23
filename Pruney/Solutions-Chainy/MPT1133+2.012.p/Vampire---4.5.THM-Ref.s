%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:29 EST 2020

% Result     : Theorem 15.97s
% Output     : Refutation 15.97s
% Verified   : 
% Statistics : Number of formulae       :  277 (112793 expanded)
%              Number of leaves         :   26 (40285 expanded)
%              Depth                    :   44
%              Number of atoms          : 1389 (1533056 expanded)
%              Number of equality atoms :   50 (116783 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21420,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f81,f113,f20980,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f20980,plain,(
    ~ v1_xboole_0(sK6(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f20449,f118])).

fof(f118,plain,(
    ! [X0,X1] : v1_funct_2(sK6(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK6(X0,X1),X0,X1)
      & v1_funct_1(sK6(X0,X1))
      & v5_relat_1(sK6(X0,X1),X1)
      & v4_relat_1(sK6(X0,X1),X0)
      & v1_relat_1(sK6(X0,X1))
      & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK6(X0,X1),X0,X1)
        & v1_funct_1(sK6(X0,X1))
        & v5_relat_1(sK6(X0,X1),X1)
        & v4_relat_1(sK6(X0,X1),X0)
        & v1_relat_1(sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f20449,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f18579,f20405])).

fof(f20405,plain,(
    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f18516,f20304])).

fof(f20304,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f20254,f81])).

fof(f20254,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f19430,f18572])).

fof(f18572,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f12673,f18364])).

fof(f18364,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f18328,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f18328,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f14505,f11565])).

fof(f11565,plain,(
    ! [X2] :
      ( v1_xboole_0(sK6(X2,u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f11223,f81])).

fof(f11223,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(sK6(X2,u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f1730,f10565])).

fof(f10565,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f10546,f85])).

fof(f10546,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f10545,f323])).

fof(f323,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f307,f97])).

fof(f307,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f77,f78])).

fof(f78,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f51])).

fof(f10545,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f10535,f2908])).

fof(f2908,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f73,f2816])).

fof(f2816,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f2815,f274])).

fof(f274,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f245,f94])).

fof(f94,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f245,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f74,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f2815,plain,
    ( v1_xboole_0(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2812,f239])).

fof(f239,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f74,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2812,plain,
    ( v1_xboole_0(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f2808,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f2808,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f2807,f72])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f2807,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f2803,f73])).

fof(f2803,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f399,f74])).

fof(f399,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1))))
      | v1_partfun1(X6,X7)
      | ~ v1_funct_2(X6,X7,u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f242,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f242,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f74,f97])).

fof(f73,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f10535,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f3204,f2922])).

fof(f2922,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f244,f2816])).

fof(f244,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f74,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3204,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(superposition,[],[f3196,f514])).

fof(f514,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f513,f274])).

fof(f513,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f512,f320])).

fof(f320,plain,(
    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f307,f119])).

fof(f512,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f354,f103])).

fof(f354,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f353,f72])).

fof(f353,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f324,f278])).

fof(f278,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f76,f78])).

fof(f76,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f324,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(resolution,[],[f307,f96])).

fof(f3196,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3195,f564])).

fof(f564,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(resolution,[],[f563,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f563,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f562,f251])).

fof(f251,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f250,f68])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f250,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f249,f69])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f249,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f248,f70])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f248,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f247,f71])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f247,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f246,f73])).

fof(f246,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f235,f72])).

fof(f235,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f74,f131])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f562,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f561,f154])).

fof(f154,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f144,f68])).

fof(f144,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f69,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f561,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f368,f425])).

fof(f425,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f142,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f142,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f69,f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f368,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f367,f70])).

fof(f367,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f366,f71])).

fof(f366,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f365,f72])).

fof(f365,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f364,f278])).

fof(f364,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f356,f307])).

fof(f356,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f310,f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f310,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f79,f78])).

fof(f79,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f3195,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f536,f576])).

fof(f576,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f575,f109])).

fof(f575,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f574,f251])).

fof(f574,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f573,f154])).

fof(f573,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f389,f425])).

fof(f389,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f388,f70])).

fof(f388,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f387,f71])).

fof(f387,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f386,f72])).

fof(f386,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f385,f278])).

fof(f385,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f377,f307])).

fof(f377,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f311,f129])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f311,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f80,f78])).

fof(f80,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f536,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    inference(resolution,[],[f257,f109])).

fof(f257,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f256,f68])).

fof(f256,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f255,f69])).

fof(f255,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f254,f70])).

fof(f254,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f253,f71])).

fof(f253,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f252,f73])).

fof(f252,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f236,f72])).

fof(f236,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f74,f130])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1730,plain,(
    ! [X2] :
      ( v1_xboole_0(sK6(X2,u1_struct_0(sK1)))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f463,f113])).

fof(f463,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f271,f97])).

fof(f271,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f270,f72])).

fof(f270,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f241,f73])).

fof(f241,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f74,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f14505,plain,(
    ~ v1_xboole_0(sK6(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    inference(resolution,[],[f12676,f118])).

fof(f12676,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f12673,f85])).

fof(f12673,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f12672,f12667])).

fof(f12667,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f11416,f11993])).

fof(f11993,plain,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f11737,f109])).

fof(f11737,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f11348,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f11348,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f10564,f10565])).

fof(f10564,plain,(
    ! [X4] : ~ r2_hidden(X4,sK2) ),
    inference(resolution,[],[f10546,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f11416,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f11415,f10565])).

fof(f11415,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f11121,f10565])).

fof(f11121,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f563,f10565])).

fof(f12672,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f12671,f12659])).

fof(f12659,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f11424,f11993])).

fof(f11424,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(forward_demodulation,[],[f11423,f10565])).

fof(f11423,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f11125,f10565])).

fof(f11125,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f575,f10565])).

fof(f12671,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f11379,f11993])).

fof(f11379,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(forward_demodulation,[],[f11378,f10565])).

fof(f11378,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f11377,f10565])).

fof(f11377,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f11069,f10565])).

fof(f11069,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f257,f10565])).

fof(f19430,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,X0,u1_struct_0(sK1))
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f18542,f85])).

fof(f18542,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1))
      | ~ v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f11667,f18364])).

fof(f11667,plain,(
    ! [X0] :
      ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f11055,f85])).

fof(f11055,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f73,f10565])).

fof(f18516,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f11408,f18364])).

fof(f11408,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f11116,f81])).

fof(f11116,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(backward_demodulation,[],[f529,f10565])).

fof(f529,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f352,f85])).

fof(f352,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f351,f72])).

fof(f351,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f322,f278])).

fof(f322,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f307,f101])).

fof(f18579,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      | ~ v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f12682,f18364])).

fof(f12682,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f12679,f85])).

fof(f12679,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f12678,f12663])).

fof(f12663,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f11412,f11993])).

fof(f11412,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f11411,f10565])).

fof(f11411,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f11119,f10565])).

fof(f11119,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(backward_demodulation,[],[f557,f10565])).

fof(f557,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f556,f263])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f262,f68])).

fof(f262,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f261,f69])).

fof(f261,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f260,f70])).

fof(f260,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f259,f71])).

fof(f259,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f258,f73])).

fof(f258,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f237,f72])).

fof(f237,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f74,f129])).

fof(f556,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f555,f185])).

fof(f185,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f175,f70])).

fof(f175,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f71,f87])).

fof(f555,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f363,f429])).

fof(f429,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f173,f99])).

fof(f173,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f71,f83])).

fof(f363,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f362,f68])).

fof(f362,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f361,f69])).

fof(f361,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f360,f72])).

fof(f360,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f359,f278])).

fof(f359,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f355,f307])).

fof(f355,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f310,f130])).

fof(f12678,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f12677,f12655])).

fof(f12655,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f11420,f11993])).

fof(f11420,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(forward_demodulation,[],[f11419,f10565])).

fof(f11419,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f11123,f10565])).

fof(f11123,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(backward_demodulation,[],[f567,f10565])).

fof(f567,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f566,f263])).

fof(f566,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f565,f185])).

fof(f565,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f384,f429])).

fof(f384,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f383,f68])).

fof(f383,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f382,f69])).

fof(f382,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f381,f72])).

fof(f381,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f380,f278])).

fof(f380,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f376,f307])).

fof(f376,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f311,f131])).

fof(f12677,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f11385,f11993])).

fof(f11385,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(forward_demodulation,[],[f11384,f10565])).

fof(f11384,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f11383,f10565])).

fof(f11383,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f11071,f10565])).

fof(f11071,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(backward_demodulation,[],[f269,f10565])).

fof(f269,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f268,f68])).

fof(f268,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f267,f69])).

fof(f267,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f266,f70])).

fof(f266,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f265,f71])).

fof(f265,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f264,f73])).

fof(f264,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f238,f72])).

fof(f238,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f74,f128])).

fof(f113,plain,(
    ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:34:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (19218)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (19239)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (19223)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (19226)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (19245)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (19221)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (19241)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (19222)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19224)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (19247)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (19233)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (19228)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (19237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (19225)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (19227)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (19230)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (19240)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.56  % (19238)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (19243)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (19219)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.56  % (19232)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.56  % (19231)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (19235)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.57  % (19235)Refutation not found, incomplete strategy% (19235)------------------------------
% 1.41/0.57  % (19235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (19235)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (19235)Memory used [KB]: 10746
% 1.41/0.57  % (19235)Time elapsed: 0.147 s
% 1.41/0.57  % (19235)------------------------------
% 1.41/0.57  % (19235)------------------------------
% 1.41/0.57  % (19246)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.57  % (19220)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.57  % (19234)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.60/0.57  % (19228)Refutation not found, incomplete strategy% (19228)------------------------------
% 1.60/0.57  % (19228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (19228)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (19228)Memory used [KB]: 10874
% 1.60/0.57  % (19228)Time elapsed: 0.137 s
% 1.60/0.57  % (19228)------------------------------
% 1.60/0.57  % (19228)------------------------------
% 1.60/0.58  % (19227)Refutation not found, incomplete strategy% (19227)------------------------------
% 1.60/0.58  % (19227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (19240)Refutation not found, incomplete strategy% (19240)------------------------------
% 1.60/0.58  % (19240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (19240)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (19240)Memory used [KB]: 11001
% 1.60/0.58  % (19240)Time elapsed: 0.152 s
% 1.60/0.58  % (19240)------------------------------
% 1.60/0.58  % (19240)------------------------------
% 1.60/0.59  % (19242)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.59  % (19227)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (19227)Memory used [KB]: 11001
% 1.60/0.59  % (19227)Time elapsed: 0.151 s
% 1.60/0.59  % (19227)------------------------------
% 1.60/0.59  % (19227)------------------------------
% 1.60/0.60  % (19244)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.60/0.60  % (19236)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.60/0.61  % (19229)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.62/0.75  % (19252)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.90/0.76  % (19251)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.90/0.78  % (19259)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.90/0.78  % (19255)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.90/0.82  % (19251)Refutation not found, incomplete strategy% (19251)------------------------------
% 2.90/0.82  % (19251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.83  % (19251)Termination reason: Refutation not found, incomplete strategy
% 2.90/0.83  
% 2.90/0.83  % (19251)Memory used [KB]: 6524
% 2.90/0.83  % (19251)Time elapsed: 0.187 s
% 2.90/0.83  % (19251)------------------------------
% 2.90/0.83  % (19251)------------------------------
% 3.52/0.84  % (19223)Time limit reached!
% 3.52/0.84  % (19223)------------------------------
% 3.52/0.84  % (19223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.84  % (19223)Termination reason: Time limit
% 3.52/0.84  
% 3.52/0.84  % (19223)Memory used [KB]: 7675
% 3.52/0.84  % (19223)Time elapsed: 0.422 s
% 3.52/0.84  % (19223)------------------------------
% 3.52/0.84  % (19223)------------------------------
% 3.52/0.84  % (19219)Refutation not found, incomplete strategy% (19219)------------------------------
% 3.52/0.84  % (19219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.84  % (19219)Termination reason: Refutation not found, incomplete strategy
% 3.52/0.84  
% 3.52/0.84  % (19219)Memory used [KB]: 6524
% 3.52/0.84  % (19219)Time elapsed: 0.409 s
% 3.52/0.84  % (19219)------------------------------
% 3.52/0.84  % (19219)------------------------------
% 3.52/0.87  % (19238)Refutation not found, incomplete strategy% (19238)------------------------------
% 3.52/0.87  % (19238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.87  % (19238)Termination reason: Refutation not found, incomplete strategy
% 3.52/0.87  
% 3.52/0.87  % (19238)Memory used [KB]: 12665
% 3.52/0.87  % (19238)Time elapsed: 0.452 s
% 3.52/0.87  % (19238)------------------------------
% 3.52/0.87  % (19238)------------------------------
% 3.75/0.89  % (19252)Refutation not found, incomplete strategy% (19252)------------------------------
% 3.75/0.89  % (19252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.89  % (19252)Termination reason: Refutation not found, incomplete strategy
% 3.75/0.89  
% 3.75/0.89  % (19252)Memory used [KB]: 6396
% 3.75/0.89  % (19252)Time elapsed: 0.222 s
% 3.75/0.89  % (19252)------------------------------
% 3.75/0.89  % (19252)------------------------------
% 3.75/0.90  % (19220)Refutation not found, incomplete strategy% (19220)------------------------------
% 3.75/0.90  % (19220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.90  % (19220)Termination reason: Refutation not found, incomplete strategy
% 3.75/0.90  
% 3.75/0.90  % (19220)Memory used [KB]: 13688
% 3.75/0.90  % (19220)Time elapsed: 0.465 s
% 3.75/0.90  % (19220)------------------------------
% 3.75/0.90  % (19220)------------------------------
% 3.75/0.93  % (19218)Time limit reached!
% 3.75/0.93  % (19218)------------------------------
% 3.75/0.93  % (19218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.93  % (19218)Termination reason: Time limit
% 3.75/0.93  % (19218)Termination phase: Saturation
% 3.75/0.93  
% 3.75/0.93  % (19218)Memory used [KB]: 2686
% 3.75/0.93  % (19218)Time elapsed: 0.500 s
% 3.75/0.93  % (19218)------------------------------
% 3.75/0.93  % (19218)------------------------------
% 3.75/0.93  % (19288)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.26/0.94  % (19230)Time limit reached!
% 4.26/0.94  % (19230)------------------------------
% 4.26/0.94  % (19230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.94  % (19230)Termination reason: Time limit
% 4.26/0.94  
% 4.26/0.94  % (19230)Memory used [KB]: 7675
% 4.26/0.94  % (19230)Time elapsed: 0.519 s
% 4.26/0.94  % (19230)------------------------------
% 4.26/0.94  % (19230)------------------------------
% 4.39/0.97  % (19286)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.39/0.97  % (19255)Refutation not found, incomplete strategy% (19255)------------------------------
% 4.39/0.97  % (19255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.98  % (19287)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.39/0.98  % (19255)Termination reason: Refutation not found, incomplete strategy
% 4.39/0.98  
% 4.39/0.98  % (19255)Memory used [KB]: 7803
% 4.39/0.98  % (19255)Time elapsed: 0.357 s
% 4.39/0.98  % (19255)------------------------------
% 4.39/0.98  % (19255)------------------------------
% 4.39/0.98  % (19286)Refutation not found, incomplete strategy% (19286)------------------------------
% 4.39/0.98  % (19286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.98  % (19286)Termination reason: Refutation not found, incomplete strategy
% 4.39/0.98  
% 4.39/0.98  % (19286)Memory used [KB]: 11001
% 4.39/0.98  % (19286)Time elapsed: 0.124 s
% 4.39/0.98  % (19286)------------------------------
% 4.39/0.98  % (19286)------------------------------
% 4.39/1.00  % (19290)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.39/1.01  % (19291)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.39/1.02  % (19293)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.84/1.02  % (19234)Time limit reached!
% 4.84/1.02  % (19234)------------------------------
% 4.84/1.02  % (19234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.02  % (19234)Termination reason: Time limit
% 4.84/1.02  
% 4.84/1.02  % (19234)Memory used [KB]: 14967
% 4.84/1.02  % (19234)Time elapsed: 0.605 s
% 4.84/1.02  % (19234)------------------------------
% 4.84/1.02  % (19234)------------------------------
% 4.84/1.03  % (19292)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.84/1.04  % (19246)Time limit reached!
% 4.84/1.04  % (19246)------------------------------
% 4.84/1.04  % (19246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.04  % (19246)Termination reason: Time limit
% 4.84/1.04  
% 4.84/1.04  % (19246)Memory used [KB]: 6780
% 4.84/1.04  % (19246)Time elapsed: 0.617 s
% 4.84/1.04  % (19246)------------------------------
% 4.84/1.04  % (19246)------------------------------
% 4.84/1.05  % (19259)Time limit reached!
% 4.84/1.05  % (19259)------------------------------
% 4.84/1.05  % (19259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.05  % (19259)Termination reason: Time limit
% 4.84/1.05  
% 4.84/1.05  % (19259)Memory used [KB]: 6652
% 4.84/1.05  % (19259)Time elapsed: 0.426 s
% 4.84/1.05  % (19259)------------------------------
% 4.84/1.05  % (19259)------------------------------
% 4.84/1.06  % (19225)Time limit reached!
% 4.84/1.06  % (19225)------------------------------
% 4.84/1.06  % (19225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.06  % (19225)Termination reason: Time limit
% 4.84/1.06  % (19225)Termination phase: Saturation
% 4.84/1.06  
% 4.84/1.06  % (19225)Memory used [KB]: 8571
% 4.84/1.06  % (19225)Time elapsed: 0.600 s
% 4.84/1.06  % (19225)------------------------------
% 4.84/1.06  % (19225)------------------------------
% 5.54/1.08  % (19294)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.54/1.09  % (19245)Refutation not found, incomplete strategy% (19245)------------------------------
% 5.54/1.09  % (19245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.54/1.09  % (19245)Termination reason: Refutation not found, incomplete strategy
% 5.54/1.09  
% 5.54/1.09  % (19245)Memory used [KB]: 8699
% 5.54/1.09  % (19245)Time elapsed: 0.682 s
% 5.54/1.09  % (19245)------------------------------
% 5.54/1.09  % (19245)------------------------------
% 5.54/1.10  % (19295)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.54/1.14  % (19296)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.54/1.15  % (19297)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.16/1.17  % (19298)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.16/1.18  % (19300)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.16/1.18  % (19299)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.45/1.23  % (19239)Time limit reached!
% 6.45/1.23  % (19239)------------------------------
% 6.45/1.23  % (19239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.45/1.23  % (19239)Termination reason: Time limit
% 6.45/1.23  
% 6.45/1.23  % (19239)Memory used [KB]: 2814
% 6.45/1.23  % (19239)Time elapsed: 0.813 s
% 6.45/1.23  % (19239)------------------------------
% 6.45/1.23  % (19239)------------------------------
% 6.90/1.25  % (19301)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 7.77/1.37  % (19310)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 8.42/1.49  % (19299)Time limit reached!
% 8.42/1.49  % (19299)------------------------------
% 8.42/1.49  % (19299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.42/1.49  % (19299)Termination reason: Time limit
% 8.42/1.49  
% 8.42/1.49  % (19299)Memory used [KB]: 3709
% 8.42/1.49  % (19299)Time elapsed: 0.409 s
% 8.42/1.49  % (19299)------------------------------
% 8.42/1.49  % (19299)------------------------------
% 8.71/1.50  % (19295)Time limit reached!
% 8.71/1.50  % (19295)------------------------------
% 8.71/1.50  % (19295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.71/1.50  % (19295)Termination reason: Time limit
% 8.71/1.50  % (19295)Termination phase: Saturation
% 8.71/1.50  
% 8.71/1.50  % (19295)Memory used [KB]: 2302
% 8.71/1.50  % (19295)Time elapsed: 0.500 s
% 8.71/1.50  % (19295)------------------------------
% 8.71/1.50  % (19295)------------------------------
% 9.11/1.61  % (19443)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 9.11/1.61  % (19437)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 9.89/1.65  % (19244)Time limit reached!
% 9.89/1.65  % (19244)------------------------------
% 9.89/1.65  % (19244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.89/1.65  % (19244)Termination reason: Time limit
% 9.89/1.65  % (19244)Termination phase: Saturation
% 9.89/1.65  
% 9.89/1.65  % (19244)Memory used [KB]: 52707
% 9.89/1.65  % (19244)Time elapsed: 1.200 s
% 9.89/1.65  % (19244)------------------------------
% 9.89/1.65  % (19244)------------------------------
% 9.89/1.65  % (19310)Time limit reached!
% 9.89/1.65  % (19310)------------------------------
% 9.89/1.65  % (19310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.89/1.65  % (19310)Termination reason: Time limit
% 9.89/1.65  
% 9.89/1.65  % (19310)Memory used [KB]: 2302
% 9.89/1.65  % (19310)Time elapsed: 0.403 s
% 9.89/1.65  % (19310)------------------------------
% 9.89/1.65  % (19310)------------------------------
% 10.32/1.74  % (19242)Time limit reached!
% 10.32/1.74  % (19242)------------------------------
% 10.32/1.74  % (19242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.32/1.74  % (19242)Termination reason: Time limit
% 10.32/1.74  
% 10.32/1.74  % (19242)Memory used [KB]: 19189
% 10.32/1.74  % (19242)Time elapsed: 1.318 s
% 10.32/1.74  % (19242)------------------------------
% 10.32/1.74  % (19242)------------------------------
% 11.00/1.78  % (19233)Time limit reached!
% 11.00/1.78  % (19233)------------------------------
% 11.00/1.78  % (19233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.00/1.78  % (19233)Termination reason: Time limit
% 11.00/1.78  
% 11.00/1.78  % (19233)Memory used [KB]: 13944
% 11.00/1.78  % (19233)Time elapsed: 1.319 s
% 11.00/1.78  % (19233)------------------------------
% 11.00/1.78  % (19233)------------------------------
% 11.00/1.79  % (19477)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 11.19/1.81  % (19485)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 11.48/1.88  % (19524)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.48/1.89  % (19512)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.48/1.90  % (19524)Refutation not found, incomplete strategy% (19524)------------------------------
% 11.48/1.90  % (19524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.48/1.90  % (19524)Termination reason: Refutation not found, incomplete strategy
% 11.48/1.90  
% 11.48/1.90  % (19524)Memory used [KB]: 6524
% 11.48/1.90  % (19524)Time elapsed: 0.071 s
% 11.48/1.90  % (19524)------------------------------
% 11.48/1.90  % (19524)------------------------------
% 12.54/1.98  % (19485)Refutation not found, incomplete strategy% (19485)------------------------------
% 12.54/1.98  % (19485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.98  % (19485)Termination reason: Refutation not found, incomplete strategy
% 12.54/1.98  
% 12.54/1.98  % (19485)Memory used [KB]: 6268
% 12.54/1.98  % (19485)Time elapsed: 0.272 s
% 12.54/1.98  % (19485)------------------------------
% 12.54/1.98  % (19485)------------------------------
% 12.54/1.98  % (19222)Time limit reached!
% 12.54/1.98  % (19222)------------------------------
% 12.54/1.98  % (19222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.98  % (19222)Termination reason: Time limit
% 12.54/1.98  
% 12.54/1.98  % (19222)Memory used [KB]: 30958
% 12.54/1.98  % (19222)Time elapsed: 1.544 s
% 12.54/1.98  % (19222)------------------------------
% 12.54/1.98  % (19222)------------------------------
% 12.54/2.01  % (19536)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.54/2.02  % (19536)Refutation not found, incomplete strategy% (19536)------------------------------
% 12.54/2.02  % (19536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/2.02  % (19536)Termination reason: Refutation not found, incomplete strategy
% 12.54/2.02  
% 12.54/2.02  % (19536)Memory used [KB]: 6396
% 12.54/2.02  % (19536)Time elapsed: 0.076 s
% 12.54/2.02  % (19536)------------------------------
% 12.54/2.02  % (19536)------------------------------
% 12.54/2.05  % (19229)Time limit reached!
% 12.54/2.05  % (19229)------------------------------
% 12.54/2.05  % (19229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/2.05  % (19229)Termination reason: Time limit
% 12.54/2.05  % (19229)Termination phase: Saturation
% 12.54/2.05  
% 12.54/2.05  % (19229)Memory used [KB]: 12281
% 12.54/2.05  % (19229)Time elapsed: 1.600 s
% 12.54/2.05  % (19229)------------------------------
% 12.54/2.05  % (19229)------------------------------
% 13.45/2.10  % (19537)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 13.72/2.12  % (19288)Time limit reached!
% 13.72/2.12  % (19288)------------------------------
% 13.72/2.12  % (19288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.07/2.14  % (19288)Termination reason: Time limit
% 14.07/2.14  
% 14.07/2.14  % (19288)Memory used [KB]: 8955
% 14.07/2.14  % (19288)Time elapsed: 1.223 s
% 14.07/2.14  % (19288)------------------------------
% 14.07/2.14  % (19288)------------------------------
% 14.07/2.19  % (19512)Time limit reached!
% 14.07/2.19  % (19512)------------------------------
% 14.07/2.19  % (19512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.07/2.19  % (19512)Termination reason: Time limit
% 14.07/2.19  
% 14.07/2.19  % (19512)Memory used [KB]: 9978
% 14.07/2.19  % (19512)Time elapsed: 0.408 s
% 14.07/2.19  % (19512)------------------------------
% 14.07/2.19  % (19512)------------------------------
% 14.69/2.28  % (19298)Time limit reached!
% 14.69/2.28  % (19298)------------------------------
% 14.69/2.28  % (19298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.69/2.28  % (19298)Termination reason: Time limit
% 14.69/2.28  
% 14.69/2.28  % (19298)Memory used [KB]: 15095
% 14.69/2.28  % (19298)Time elapsed: 1.221 s
% 14.69/2.28  % (19298)------------------------------
% 14.69/2.28  % (19298)------------------------------
% 14.69/2.28  % (19232)Time limit reached!
% 14.69/2.28  % (19232)------------------------------
% 14.69/2.28  % (19232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.69/2.28  % (19232)Termination reason: Time limit
% 14.69/2.28  
% 14.69/2.28  % (19232)Memory used [KB]: 6140
% 14.69/2.28  % (19232)Time elapsed: 1.842 s
% 14.69/2.28  % (19232)------------------------------
% 14.69/2.28  % (19232)------------------------------
% 15.97/2.40  % (19294)Refutation found. Thanks to Tanya!
% 15.97/2.40  % SZS status Theorem for theBenchmark
% 15.97/2.40  % SZS output start Proof for theBenchmark
% 15.97/2.40  fof(f21420,plain,(
% 15.97/2.40    $false),
% 15.97/2.40    inference(unit_resulting_resolution,[],[f81,f113,f20980,f97])).
% 15.97/2.40  fof(f97,plain,(
% 15.97/2.40    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f37])).
% 15.97/2.40  fof(f37,plain,(
% 15.97/2.40    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 15.97/2.40    inference(ennf_transformation,[],[f11])).
% 15.97/2.40  fof(f11,axiom,(
% 15.97/2.40    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 15.97/2.40  fof(f20980,plain,(
% 15.97/2.40    ~v1_xboole_0(sK6(k1_xboole_0,k1_xboole_0))),
% 15.97/2.40    inference(resolution,[],[f20449,f118])).
% 15.97/2.40  fof(f118,plain,(
% 15.97/2.40    ( ! [X0,X1] : (v1_funct_2(sK6(X0,X1),X0,X1)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f67])).
% 15.97/2.40  fof(f67,plain,(
% 15.97/2.40    ! [X0,X1] : (v1_funct_2(sK6(X0,X1),X0,X1) & v1_funct_1(sK6(X0,X1)) & v5_relat_1(sK6(X0,X1),X1) & v4_relat_1(sK6(X0,X1),X0) & v1_relat_1(sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.97/2.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f66])).
% 15.97/2.40  fof(f66,plain,(
% 15.97/2.40    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK6(X0,X1),X0,X1) & v1_funct_1(sK6(X0,X1)) & v5_relat_1(sK6(X0,X1),X1) & v4_relat_1(sK6(X0,X1),X0) & v1_relat_1(sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f15,axiom,(
% 15.97/2.40    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 15.97/2.40  fof(f20449,plain,(
% 15.97/2.40    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(backward_demodulation,[],[f18579,f20405])).
% 15.97/2.40  fof(f20405,plain,(
% 15.97/2.40    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f18516,f20304])).
% 15.97/2.40  fof(f20304,plain,(
% 15.97/2.40    ~v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f20254,f81])).
% 15.97/2.40  fof(f20254,plain,(
% 15.97/2.40    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 15.97/2.40    inference(resolution,[],[f19430,f18572])).
% 15.97/2.40  fof(f18572,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(backward_demodulation,[],[f12673,f18364])).
% 15.97/2.40  fof(f18364,plain,(
% 15.97/2.40    k1_xboole_0 = u1_struct_0(sK0)),
% 15.97/2.40    inference(resolution,[],[f18328,f85])).
% 15.97/2.40  fof(f85,plain,(
% 15.97/2.40    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f28])).
% 15.97/2.40  fof(f28,plain,(
% 15.97/2.40    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 15.97/2.40    inference(ennf_transformation,[],[f4])).
% 15.97/2.40  fof(f4,axiom,(
% 15.97/2.40    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 15.97/2.40  fof(f18328,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(sK0))),
% 15.97/2.40    inference(resolution,[],[f14505,f11565])).
% 15.97/2.40  fof(f11565,plain,(
% 15.97/2.40    ( ! [X2] : (v1_xboole_0(sK6(X2,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK0))) )),
% 15.97/2.40    inference(subsumption_resolution,[],[f11223,f81])).
% 15.97/2.40  fof(f11223,plain,(
% 15.97/2.40    ( ! [X2] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK6(X2,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK0))) )),
% 15.97/2.40    inference(backward_demodulation,[],[f1730,f10565])).
% 15.97/2.40  fof(f10565,plain,(
% 15.97/2.40    k1_xboole_0 = sK2),
% 15.97/2.40    inference(resolution,[],[f10546,f85])).
% 15.97/2.40  fof(f10546,plain,(
% 15.97/2.40    v1_xboole_0(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f10545,f323])).
% 15.97/2.40  fof(f323,plain,(
% 15.97/2.40    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(resolution,[],[f307,f97])).
% 15.97/2.40  fof(f307,plain,(
% 15.97/2.40    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 15.97/2.40    inference(forward_demodulation,[],[f77,f78])).
% 15.97/2.40  fof(f78,plain,(
% 15.97/2.40    sK2 = sK3),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f51,plain,(
% 15.97/2.40    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 15.97/2.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49,f48,f47])).
% 15.97/2.40  fof(f47,plain,(
% 15.97/2.40    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f48,plain,(
% 15.97/2.40    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f49,plain,(
% 15.97/2.40    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f50,plain,(
% 15.97/2.40    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f46,plain,(
% 15.97/2.40    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.97/2.40    inference(flattening,[],[f45])).
% 15.97/2.40  fof(f45,plain,(
% 15.97/2.40    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.97/2.40    inference(nnf_transformation,[],[f24])).
% 15.97/2.40  fof(f24,plain,(
% 15.97/2.40    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.97/2.40    inference(flattening,[],[f23])).
% 15.97/2.40  fof(f23,plain,(
% 15.97/2.40    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.97/2.40    inference(ennf_transformation,[],[f22])).
% 15.97/2.40  fof(f22,negated_conjecture,(
% 15.97/2.40    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.97/2.40    inference(negated_conjecture,[],[f21])).
% 15.97/2.40  fof(f21,conjecture,(
% 15.97/2.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 15.97/2.40  fof(f77,plain,(
% 15.97/2.40    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f10545,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f10535,f2908])).
% 15.97/2.40  fof(f2908,plain,(
% 15.97/2.40    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(superposition,[],[f73,f2816])).
% 15.97/2.40  fof(f2816,plain,(
% 15.97/2.40    u1_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f2815,f274])).
% 15.97/2.40  fof(f274,plain,(
% 15.97/2.40    v1_relat_1(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f245,f94])).
% 15.97/2.40  fof(f94,plain,(
% 15.97/2.40    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.97/2.40    inference(cnf_transformation,[],[f8])).
% 15.97/2.40  fof(f8,axiom,(
% 15.97/2.40    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 15.97/2.40  fof(f245,plain,(
% 15.97/2.40    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 15.97/2.40    inference(resolution,[],[f74,f82])).
% 15.97/2.40  fof(f82,plain,(
% 15.97/2.40    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f25])).
% 15.97/2.40  fof(f25,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.97/2.40    inference(ennf_transformation,[],[f7])).
% 15.97/2.40  fof(f7,axiom,(
% 15.97/2.40    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 15.97/2.40  fof(f74,plain,(
% 15.97/2.40    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f2815,plain,(
% 15.97/2.40    v1_xboole_0(sK2) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f2812,f239])).
% 15.97/2.40  fof(f239,plain,(
% 15.97/2.40    v4_relat_1(sK2,u1_struct_0(sK0))),
% 15.97/2.40    inference(resolution,[],[f74,f119])).
% 15.97/2.40  fof(f119,plain,(
% 15.97/2.40    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.97/2.40    inference(cnf_transformation,[],[f44])).
% 15.97/2.40  fof(f44,plain,(
% 15.97/2.40    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.97/2.40    inference(ennf_transformation,[],[f10])).
% 15.97/2.40  fof(f10,axiom,(
% 15.97/2.40    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 15.97/2.40  fof(f2812,plain,(
% 15.97/2.40    v1_xboole_0(sK2) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 15.97/2.40    inference(resolution,[],[f2808,f103])).
% 15.97/2.40  fof(f103,plain,(
% 15.97/2.40    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f58])).
% 15.97/2.40  fof(f58,plain,(
% 15.97/2.40    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.97/2.40    inference(nnf_transformation,[],[f42])).
% 15.97/2.40  fof(f42,plain,(
% 15.97/2.40    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.97/2.40    inference(flattening,[],[f41])).
% 15.97/2.40  fof(f41,plain,(
% 15.97/2.40    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.97/2.40    inference(ennf_transformation,[],[f14])).
% 15.97/2.40  fof(f14,axiom,(
% 15.97/2.40    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 15.97/2.40  fof(f2808,plain,(
% 15.97/2.40    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f2807,f72])).
% 15.97/2.40  fof(f72,plain,(
% 15.97/2.40    v1_funct_1(sK2)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f2807,plain,(
% 15.97/2.40    v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_1(sK2) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f2803,f73])).
% 15.97/2.40  fof(f2803,plain,(
% 15.97/2.40    v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(resolution,[],[f399,f74])).
% 15.97/2.40  fof(f399,plain,(
% 15.97/2.40    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1)))) | v1_partfun1(X6,X7) | ~v1_funct_2(X6,X7,u1_struct_0(sK1)) | ~v1_funct_1(X6) | v1_xboole_0(sK2)) )),
% 15.97/2.40    inference(resolution,[],[f242,f96])).
% 15.97/2.40  fof(f96,plain,(
% 15.97/2.40    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f36])).
% 15.97/2.40  fof(f36,plain,(
% 15.97/2.40    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.97/2.40    inference(flattening,[],[f35])).
% 15.97/2.40  fof(f35,plain,(
% 15.97/2.40    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.97/2.40    inference(ennf_transformation,[],[f12])).
% 15.97/2.40  fof(f12,axiom,(
% 15.97/2.40    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 15.97/2.40  fof(f242,plain,(
% 15.97/2.40    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(resolution,[],[f74,f97])).
% 15.97/2.40  fof(f73,plain,(
% 15.97/2.40    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f10535,plain,(
% 15.97/2.40    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(resolution,[],[f3204,f2922])).
% 15.97/2.40  fof(f2922,plain,(
% 15.97/2.40    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | v1_xboole_0(sK2)),
% 15.97/2.40    inference(superposition,[],[f244,f2816])).
% 15.97/2.40  fof(f244,plain,(
% 15.97/2.40    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 15.97/2.40    inference(resolution,[],[f74,f108])).
% 15.97/2.40  fof(f108,plain,(
% 15.97/2.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.97/2.40    inference(cnf_transformation,[],[f63])).
% 15.97/2.40  fof(f63,plain,(
% 15.97/2.40    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.97/2.40    inference(nnf_transformation,[],[f6])).
% 15.97/2.40  fof(f6,axiom,(
% 15.97/2.40    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 15.97/2.40  fof(f3204,plain,(
% 15.97/2.40    ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(superposition,[],[f3196,f514])).
% 15.97/2.40  fof(f514,plain,(
% 15.97/2.40    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f513,f274])).
% 15.97/2.40  fof(f513,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 15.97/2.40    inference(subsumption_resolution,[],[f512,f320])).
% 15.97/2.40  fof(f320,plain,(
% 15.97/2.40    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 15.97/2.40    inference(resolution,[],[f307,f119])).
% 15.97/2.40  fof(f512,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(sK2)),
% 15.97/2.40    inference(resolution,[],[f354,f103])).
% 15.97/2.40  fof(f354,plain,(
% 15.97/2.40    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f353,f72])).
% 15.97/2.40  fof(f353,plain,(
% 15.97/2.40    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f324,f278])).
% 15.97/2.40  fof(f278,plain,(
% 15.97/2.40    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(forward_demodulation,[],[f76,f78])).
% 15.97/2.40  fof(f76,plain,(
% 15.97/2.40    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f324,plain,(
% 15.97/2.40    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(resolution,[],[f307,f96])).
% 15.97/2.40  fof(f3196,plain,(
% 15.97/2.40    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f3195,f564])).
% 15.97/2.40  fof(f564,plain,(
% 15.97/2.40    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 15.97/2.40    inference(resolution,[],[f563,f109])).
% 15.97/2.40  fof(f109,plain,(
% 15.97/2.40    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f63])).
% 15.97/2.40  fof(f563,plain,(
% 15.97/2.40    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f562,f251])).
% 15.97/2.40  fof(f251,plain,(
% 15.97/2.40    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f250,f68])).
% 15.97/2.40  fof(f68,plain,(
% 15.97/2.40    v2_pre_topc(sK0)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f250,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f249,f69])).
% 15.97/2.40  fof(f69,plain,(
% 15.97/2.40    l1_pre_topc(sK0)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f249,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f248,f70])).
% 15.97/2.40  fof(f70,plain,(
% 15.97/2.40    v2_pre_topc(sK1)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f248,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f247,f71])).
% 15.97/2.40  fof(f71,plain,(
% 15.97/2.40    l1_pre_topc(sK1)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f247,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f246,f73])).
% 15.97/2.40  fof(f246,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f235,f72])).
% 15.97/2.40  fof(f235,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(resolution,[],[f74,f131])).
% 15.97/2.40  fof(f131,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(duplicate_literal_removal,[],[f124])).
% 15.97/2.40  fof(f124,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(equality_resolution,[],[f90])).
% 15.97/2.40  fof(f90,plain,(
% 15.97/2.40    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f53])).
% 15.97/2.40  fof(f53,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.97/2.40    inference(nnf_transformation,[],[f34])).
% 15.97/2.40  fof(f34,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.97/2.40    inference(flattening,[],[f33])).
% 15.97/2.40  fof(f33,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.97/2.40    inference(ennf_transformation,[],[f19])).
% 15.97/2.40  fof(f19,axiom,(
% 15.97/2.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 15.97/2.40  fof(f562,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f561,f154])).
% 15.97/2.40  fof(f154,plain,(
% 15.97/2.40    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f144,f68])).
% 15.97/2.40  fof(f144,plain,(
% 15.97/2.40    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(resolution,[],[f69,f87])).
% 15.97/2.40  fof(f87,plain,(
% 15.97/2.40    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f30])).
% 15.97/2.40  fof(f30,plain,(
% 15.97/2.40    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.97/2.40    inference(flattening,[],[f29])).
% 15.97/2.40  fof(f29,plain,(
% 15.97/2.40    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.97/2.40    inference(ennf_transformation,[],[f18])).
% 15.97/2.40  fof(f18,axiom,(
% 15.97/2.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 15.97/2.40  fof(f561,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f368,f425])).
% 15.97/2.40  fof(f425,plain,(
% 15.97/2.40    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(resolution,[],[f142,f99])).
% 15.97/2.40  fof(f99,plain,(
% 15.97/2.40    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.97/2.40    inference(cnf_transformation,[],[f38])).
% 15.97/2.40  fof(f38,plain,(
% 15.97/2.40    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.97/2.40    inference(ennf_transformation,[],[f16])).
% 15.97/2.40  fof(f16,axiom,(
% 15.97/2.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 15.97/2.40  fof(f142,plain,(
% 15.97/2.40    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 15.97/2.40    inference(resolution,[],[f69,f83])).
% 15.97/2.40  fof(f83,plain,(
% 15.97/2.40    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f26])).
% 15.97/2.40  fof(f26,plain,(
% 15.97/2.40    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.97/2.40    inference(ennf_transformation,[],[f17])).
% 15.97/2.40  fof(f17,axiom,(
% 15.97/2.40    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 15.97/2.40  fof(f368,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f367,f70])).
% 15.97/2.40  fof(f367,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f366,f71])).
% 15.97/2.40  fof(f366,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f365,f72])).
% 15.97/2.40  fof(f365,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f364,f278])).
% 15.97/2.40  fof(f364,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f356,f307])).
% 15.97/2.40  fof(f356,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(resolution,[],[f310,f128])).
% 15.97/2.40  fof(f128,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(duplicate_literal_removal,[],[f121])).
% 15.97/2.40  fof(f121,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(equality_resolution,[],[f89])).
% 15.97/2.40  fof(f89,plain,(
% 15.97/2.40    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f52])).
% 15.97/2.40  fof(f52,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.97/2.40    inference(nnf_transformation,[],[f32])).
% 15.97/2.40  fof(f32,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.97/2.40    inference(flattening,[],[f31])).
% 15.97/2.40  fof(f31,plain,(
% 15.97/2.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.97/2.40    inference(ennf_transformation,[],[f20])).
% 15.97/2.40  fof(f20,axiom,(
% 15.97/2.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 15.97/2.40  fof(f310,plain,(
% 15.97/2.40    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 15.97/2.40    inference(forward_demodulation,[],[f79,f78])).
% 15.97/2.40  fof(f79,plain,(
% 15.97/2.40    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f3195,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f536,f576])).
% 15.97/2.40  fof(f576,plain,(
% 15.97/2.40    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 15.97/2.40    inference(resolution,[],[f575,f109])).
% 15.97/2.40  fof(f575,plain,(
% 15.97/2.40    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f574,f251])).
% 15.97/2.40  fof(f574,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f573,f154])).
% 15.97/2.40  fof(f573,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f389,f425])).
% 15.97/2.40  fof(f389,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f388,f70])).
% 15.97/2.40  fof(f388,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f387,f71])).
% 15.97/2.40  fof(f387,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f386,f72])).
% 15.97/2.40  fof(f386,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f385,f278])).
% 15.97/2.40  fof(f385,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f377,f307])).
% 15.97/2.40  fof(f377,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 15.97/2.40    inference(resolution,[],[f311,f129])).
% 15.97/2.40  fof(f129,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(duplicate_literal_removal,[],[f122])).
% 15.97/2.40  fof(f122,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(equality_resolution,[],[f88])).
% 15.97/2.40  fof(f88,plain,(
% 15.97/2.40    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f52])).
% 15.97/2.40  fof(f311,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 15.97/2.40    inference(forward_demodulation,[],[f80,f78])).
% 15.97/2.40  fof(f80,plain,(
% 15.97/2.40    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 15.97/2.40    inference(cnf_transformation,[],[f51])).
% 15.97/2.40  fof(f536,plain,(
% 15.97/2.40    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))),
% 15.97/2.40    inference(resolution,[],[f257,f109])).
% 15.97/2.40  fof(f257,plain,(
% 15.97/2.40    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f256,f68])).
% 15.97/2.40  fof(f256,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f255,f69])).
% 15.97/2.40  fof(f255,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f254,f70])).
% 15.97/2.40  fof(f254,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f253,f71])).
% 15.97/2.40  fof(f253,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f252,f73])).
% 15.97/2.40  fof(f252,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(subsumption_resolution,[],[f236,f72])).
% 15.97/2.40  fof(f236,plain,(
% 15.97/2.40    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.40    inference(resolution,[],[f74,f130])).
% 15.97/2.40  fof(f130,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(duplicate_literal_removal,[],[f123])).
% 15.97/2.40  fof(f123,plain,(
% 15.97/2.40    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(equality_resolution,[],[f91])).
% 15.97/2.40  fof(f91,plain,(
% 15.97/2.40    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f53])).
% 15.97/2.40  fof(f1730,plain,(
% 15.97/2.40    ( ! [X2] : (v1_xboole_0(sK6(X2,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_xboole_0(sK2)) )),
% 15.97/2.40    inference(resolution,[],[f463,f113])).
% 15.97/2.40  fof(f463,plain,(
% 15.97/2.40    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(X2) | ~v1_xboole_0(sK2)) )),
% 15.97/2.40    inference(resolution,[],[f271,f97])).
% 15.97/2.40  fof(f271,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(sK1)) | ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 15.97/2.40    inference(subsumption_resolution,[],[f270,f72])).
% 15.97/2.40  fof(f270,plain,(
% 15.97/2.40    ~v1_xboole_0(sK2) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 15.97/2.40    inference(subsumption_resolution,[],[f241,f73])).
% 15.97/2.40  fof(f241,plain,(
% 15.97/2.40    ~v1_xboole_0(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 15.97/2.40    inference(resolution,[],[f74,f101])).
% 15.97/2.40  fof(f101,plain,(
% 15.97/2.40    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f40])).
% 15.97/2.40  fof(f40,plain,(
% 15.97/2.40    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.97/2.40    inference(flattening,[],[f39])).
% 15.97/2.40  fof(f39,plain,(
% 15.97/2.40    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.97/2.40    inference(ennf_transformation,[],[f13])).
% 15.97/2.40  fof(f13,axiom,(
% 15.97/2.40    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 15.97/2.40  fof(f14505,plain,(
% 15.97/2.40    ~v1_xboole_0(sK6(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))),
% 15.97/2.40    inference(resolution,[],[f12676,f118])).
% 15.97/2.40  fof(f12676,plain,(
% 15.97/2.40    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(superposition,[],[f12673,f85])).
% 15.97/2.40  fof(f12673,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(subsumption_resolution,[],[f12672,f12667])).
% 15.97/2.40  fof(f12667,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 15.97/2.40    inference(subsumption_resolution,[],[f11416,f11993])).
% 15.97/2.40  fof(f11993,plain,(
% 15.97/2.40    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 15.97/2.40    inference(resolution,[],[f11737,f109])).
% 15.97/2.40  fof(f11737,plain,(
% 15.97/2.40    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.97/2.40    inference(resolution,[],[f11348,f106])).
% 15.97/2.40  fof(f106,plain,(
% 15.97/2.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f62])).
% 15.97/2.40  fof(f62,plain,(
% 15.97/2.40    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.97/2.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).
% 15.97/2.40  fof(f61,plain,(
% 15.97/2.40    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f60,plain,(
% 15.97/2.40    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.97/2.40    inference(rectify,[],[f59])).
% 15.97/2.40  fof(f59,plain,(
% 15.97/2.40    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.97/2.40    inference(nnf_transformation,[],[f43])).
% 15.97/2.40  fof(f43,plain,(
% 15.97/2.40    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.97/2.40    inference(ennf_transformation,[],[f2])).
% 15.97/2.40  fof(f2,axiom,(
% 15.97/2.40    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 15.97/2.40  fof(f11348,plain,(
% 15.97/2.40    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 15.97/2.40    inference(backward_demodulation,[],[f10564,f10565])).
% 15.97/2.40  fof(f10564,plain,(
% 15.97/2.40    ( ! [X4] : (~r2_hidden(X4,sK2)) )),
% 15.97/2.40    inference(resolution,[],[f10546,f92])).
% 15.97/2.40  fof(f92,plain,(
% 15.97/2.40    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(cnf_transformation,[],[f57])).
% 15.97/2.40  fof(f57,plain,(
% 15.97/2.40    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.97/2.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 15.97/2.40  fof(f56,plain,(
% 15.97/2.40    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 15.97/2.40    introduced(choice_axiom,[])).
% 15.97/2.40  fof(f55,plain,(
% 15.97/2.40    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.97/2.40    inference(rectify,[],[f54])).
% 15.97/2.40  fof(f54,plain,(
% 15.97/2.40    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 15.97/2.40    inference(nnf_transformation,[],[f1])).
% 15.97/2.40  fof(f1,axiom,(
% 15.97/2.40    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.97/2.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 15.97/2.40  fof(f11416,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 15.97/2.40    inference(forward_demodulation,[],[f11415,f10565])).
% 15.97/2.40  fof(f11415,plain,(
% 15.97/2.40    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(forward_demodulation,[],[f11121,f10565])).
% 15.97/2.40  fof(f11121,plain,(
% 15.97/2.40    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(backward_demodulation,[],[f563,f10565])).
% 15.97/2.40  fof(f12672,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 15.97/2.40    inference(subsumption_resolution,[],[f12671,f12659])).
% 15.97/2.40  fof(f12659,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.40    inference(subsumption_resolution,[],[f11424,f11993])).
% 15.97/2.40  fof(f11424,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.40    inference(forward_demodulation,[],[f11423,f10565])).
% 15.97/2.40  fof(f11423,plain,(
% 15.97/2.40    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(forward_demodulation,[],[f11125,f10565])).
% 15.97/2.40  fof(f11125,plain,(
% 15.97/2.40    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(backward_demodulation,[],[f575,f10565])).
% 15.97/2.40  fof(f12671,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.40    inference(subsumption_resolution,[],[f11379,f11993])).
% 15.97/2.40  fof(f11379,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.40    inference(forward_demodulation,[],[f11378,f10565])).
% 15.97/2.40  fof(f11378,plain,(
% 15.97/2.40    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(forward_demodulation,[],[f11377,f10565])).
% 15.97/2.40  fof(f11377,plain,(
% 15.97/2.40    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(forward_demodulation,[],[f11069,f10565])).
% 15.97/2.40  fof(f11069,plain,(
% 15.97/2.40    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 15.97/2.40    inference(backward_demodulation,[],[f257,f10565])).
% 15.97/2.40  fof(f19430,plain,(
% 15.97/2.40    ( ! [X0,X1] : (v1_funct_2(X1,X0,u1_struct_0(sK1)) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(superposition,[],[f18542,f85])).
% 15.97/2.40  fof(f18542,plain,(
% 15.97/2.40    ( ! [X0] : (v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(backward_demodulation,[],[f11667,f18364])).
% 15.97/2.40  fof(f11667,plain,(
% 15.97/2.40    ( ! [X0] : (v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(superposition,[],[f11055,f85])).
% 15.97/2.40  fof(f11055,plain,(
% 15.97/2.40    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 15.97/2.40    inference(backward_demodulation,[],[f73,f10565])).
% 15.97/2.40  fof(f18516,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.40    inference(backward_demodulation,[],[f11408,f18364])).
% 15.97/2.40  fof(f11408,plain,(
% 15.97/2.40    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f11116,f81])).
% 15.97/2.40  fof(f11116,plain,(
% 15.97/2.40    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 15.97/2.40    inference(backward_demodulation,[],[f529,f10565])).
% 15.97/2.40  fof(f529,plain,(
% 15.97/2.40    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_xboole_0(sK2)),
% 15.97/2.40    inference(resolution,[],[f352,f85])).
% 15.97/2.40  fof(f352,plain,(
% 15.97/2.40    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f351,f72])).
% 15.97/2.40  fof(f351,plain,(
% 15.97/2.40    ~v1_xboole_0(sK2) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f322,f278])).
% 15.97/2.40  fof(f322,plain,(
% 15.97/2.40    ~v1_xboole_0(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 15.97/2.40    inference(resolution,[],[f307,f101])).
% 15.97/2.40  fof(f18579,plain,(
% 15.97/2.40    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(backward_demodulation,[],[f12682,f18364])).
% 15.97/2.40  fof(f12682,plain,(
% 15.97/2.40    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_xboole_0(X0)) )),
% 15.97/2.40    inference(superposition,[],[f12679,f85])).
% 15.97/2.40  fof(f12679,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f12678,f12663])).
% 15.97/2.40  fof(f12663,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.40    inference(subsumption_resolution,[],[f11412,f11993])).
% 15.97/2.40  fof(f11412,plain,(
% 15.97/2.40    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 15.97/2.40    inference(forward_demodulation,[],[f11411,f10565])).
% 15.97/2.40  fof(f11411,plain,(
% 15.97/2.40    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(forward_demodulation,[],[f11119,f10565])).
% 15.97/2.40  fof(f11119,plain,(
% 15.97/2.40    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(backward_demodulation,[],[f557,f10565])).
% 15.97/2.40  fof(f557,plain,(
% 15.97/2.40    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.40    inference(subsumption_resolution,[],[f556,f263])).
% 15.97/2.41  fof(f263,plain,(
% 15.97/2.41    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(subsumption_resolution,[],[f262,f68])).
% 15.97/2.41  fof(f262,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f261,f69])).
% 15.97/2.41  fof(f261,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f260,f70])).
% 15.97/2.41  fof(f260,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f259,f71])).
% 15.97/2.41  fof(f259,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f258,f73])).
% 15.97/2.41  fof(f258,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f237,f72])).
% 15.97/2.41  fof(f237,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(resolution,[],[f74,f129])).
% 15.97/2.41  fof(f556,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(subsumption_resolution,[],[f555,f185])).
% 15.97/2.41  fof(f185,plain,(
% 15.97/2.41    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(subsumption_resolution,[],[f175,f70])).
% 15.97/2.41  fof(f175,plain,(
% 15.97/2.41    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1)),
% 15.97/2.41    inference(resolution,[],[f71,f87])).
% 15.97/2.41  fof(f555,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(subsumption_resolution,[],[f363,f429])).
% 15.97/2.41  fof(f429,plain,(
% 15.97/2.41    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(resolution,[],[f173,f99])).
% 15.97/2.41  fof(f173,plain,(
% 15.97/2.41    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 15.97/2.41    inference(resolution,[],[f71,f83])).
% 15.97/2.41  fof(f363,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(subsumption_resolution,[],[f362,f68])).
% 15.97/2.41  fof(f362,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f361,f69])).
% 15.97/2.41  fof(f361,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f360,f72])).
% 15.97/2.41  fof(f360,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f359,f278])).
% 15.97/2.41  fof(f359,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f355,f307])).
% 15.97/2.41  fof(f355,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(resolution,[],[f310,f130])).
% 15.97/2.41  fof(f12678,plain,(
% 15.97/2.41    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(subsumption_resolution,[],[f12677,f12655])).
% 15.97/2.41  fof(f12655,plain,(
% 15.97/2.41    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.41    inference(subsumption_resolution,[],[f11420,f11993])).
% 15.97/2.41  fof(f11420,plain,(
% 15.97/2.41    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.41    inference(forward_demodulation,[],[f11419,f10565])).
% 15.97/2.41  fof(f11419,plain,(
% 15.97/2.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(forward_demodulation,[],[f11123,f10565])).
% 15.97/2.41  fof(f11123,plain,(
% 15.97/2.41    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(backward_demodulation,[],[f567,f10565])).
% 15.97/2.41  fof(f567,plain,(
% 15.97/2.41    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(subsumption_resolution,[],[f566,f263])).
% 15.97/2.41  fof(f566,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(subsumption_resolution,[],[f565,f185])).
% 15.97/2.41  fof(f565,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(subsumption_resolution,[],[f384,f429])).
% 15.97/2.41  fof(f384,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 15.97/2.41    inference(subsumption_resolution,[],[f383,f68])).
% 15.97/2.41  fof(f383,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f382,f69])).
% 15.97/2.41  fof(f382,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f381,f72])).
% 15.97/2.41  fof(f381,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f380,f278])).
% 15.97/2.41  fof(f380,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f376,f307])).
% 15.97/2.41  fof(f376,plain,(
% 15.97/2.41    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(resolution,[],[f311,f131])).
% 15.97/2.41  fof(f12677,plain,(
% 15.97/2.41    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.41    inference(subsumption_resolution,[],[f11385,f11993])).
% 15.97/2.41  fof(f11385,plain,(
% 15.97/2.41    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 15.97/2.41    inference(forward_demodulation,[],[f11384,f10565])).
% 15.97/2.41  fof(f11384,plain,(
% 15.97/2.41    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(forward_demodulation,[],[f11383,f10565])).
% 15.97/2.41  fof(f11383,plain,(
% 15.97/2.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(forward_demodulation,[],[f11071,f10565])).
% 15.97/2.41  fof(f11071,plain,(
% 15.97/2.41    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(backward_demodulation,[],[f269,f10565])).
% 15.97/2.41  fof(f269,plain,(
% 15.97/2.41    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 15.97/2.41    inference(subsumption_resolution,[],[f268,f68])).
% 15.97/2.41  fof(f268,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f267,f69])).
% 15.97/2.41  fof(f267,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f266,f70])).
% 15.97/2.41  fof(f266,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f265,f71])).
% 15.97/2.41  fof(f265,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f264,f73])).
% 15.97/2.41  fof(f264,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(subsumption_resolution,[],[f238,f72])).
% 15.97/2.41  fof(f238,plain,(
% 15.97/2.41    v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 15.97/2.41    inference(resolution,[],[f74,f128])).
% 15.97/2.41  fof(f113,plain,(
% 15.97/2.41    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.97/2.41    inference(cnf_transformation,[],[f67])).
% 15.97/2.41  fof(f81,plain,(
% 15.97/2.41    v1_xboole_0(k1_xboole_0)),
% 15.97/2.41    inference(cnf_transformation,[],[f3])).
% 15.97/2.41  fof(f3,axiom,(
% 15.97/2.41    v1_xboole_0(k1_xboole_0)),
% 15.97/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 15.97/2.41  % SZS output end Proof for theBenchmark
% 15.97/2.41  % (19294)------------------------------
% 15.97/2.41  % (19294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.97/2.41  % (19294)Termination reason: Refutation
% 15.97/2.41  
% 15.97/2.41  % (19294)Memory used [KB]: 12920
% 15.97/2.41  % (19294)Time elapsed: 1.438 s
% 15.97/2.41  % (19294)------------------------------
% 15.97/2.41  % (19294)------------------------------
% 15.97/2.41  % (19217)Success in time 2.029 s
%------------------------------------------------------------------------------
