%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 970 expanded)
%              Number of leaves         :   32 ( 368 expanded)
%              Depth                    :   26
%              Number of atoms          :  727 (8071 expanded)
%              Number of equality atoms :   85 ( 276 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f217,f256,f307,f310,f399,f467])).

fof(f467,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f465,f443])).

fof(f443,plain,
    ( r2_funct_2(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f349,f418])).

fof(f418,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f417,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f417,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f255,f332])).

fof(f332,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(resolution,[],[f316,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
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

fof(f316,plain,
    ( v1_xboole_0(k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f150,f216])).

fof(f216,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl7_6
  <=> u1_struct_0(sK1) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f150,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl7_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f255,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl7_12
  <=> sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f349,plain,
    ( r2_funct_2(u1_struct_0(sK2),k1_xboole_0,sK3,sK3)
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f319,f332])).

fof(f319,plain,
    ( r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK3),sK3,sK3)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f161,f216])).

fof(f161,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) ),
    inference(subsumption_resolution,[],[f160,f76])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f160,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f137,f77])).

fof(f77,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f78,f122])).

fof(f122,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f465,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f444,f458])).

fof(f458,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f457,f342])).

fof(f342,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f311,f332])).

fof(f311,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK3))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f268,f150])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f207,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
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

fof(f207,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f177,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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

fof(f177,plain,(
    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f176,f132])).

fof(f132,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f176,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f134,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

% (11608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f134,plain,(
    v5_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f78,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f457,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_xboole_0,k7_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f437,f418])).

fof(f437,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | r2_hidden(sK5(sK3,k7_relat_1(sK3,X0)),sK3) )
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f286,f418])).

fof(f286,plain,(
    ! [X0] :
      ( sK3 = k7_relat_1(sK3,X0)
      | r2_hidden(sK5(sK3,k7_relat_1(sK3,X0)),sK3) ) ),
    inference(resolution,[],[f205,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f205,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK3,k7_relat_1(sK3,X2))
      | sK3 = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f171,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f171,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(resolution,[],[f132,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f444,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0,k7_relat_1(k1_xboole_0,u1_struct_0(sK2)))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f351,f418])).

fof(f351,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k1_xboole_0,sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f328,f332])).

fof(f328,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK3),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f308,f216])).

fof(f308,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f79,f302])).

fof(f302,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f301,f75])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f301,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f263,f127])).

fof(f127,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f126,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f126,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f125,f70])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f125,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f75,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f263,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f262,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f262,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f261,f69])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f261,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f258,f70])).

fof(f258,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f159,f75])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,X1)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k7_relat_1(sK3,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(backward_demodulation,[],[f144,f158])).

fof(f158,plain,(
    ! [X3] : k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k7_relat_1(sK3,X3) ),
    inference(subsumption_resolution,[],[f136,f76])).

fof(f136,plain,(
    ! [X3] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k7_relat_1(sK3,X3)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f78,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

% (11621)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f143,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f142,f72])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f141,f73])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f140,f76])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ v1_funct_1(sK3)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f130,f77])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK3)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f78,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f79,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f399,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | spl7_11 ),
    inference(subsumption_resolution,[],[f395,f80])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f395,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_6
    | spl7_11 ),
    inference(resolution,[],[f357,f87])).

fof(f357,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_6
    | spl7_11 ),
    inference(forward_demodulation,[],[f338,f117])).

fof(f338,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3),k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))
    | ~ spl7_1
    | ~ spl7_6
    | spl7_11 ),
    inference(backward_demodulation,[],[f264,f332])).

fof(f264,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3),k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | spl7_11 ),
    inference(resolution,[],[f251,f100])).

fof(f251,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl7_11
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f310,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl7_1
    | spl7_5 ),
    inference(subsumption_resolution,[],[f150,f282])).

fof(f282,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl7_5 ),
    inference(resolution,[],[f231,f87])).

fof(f231,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),k2_relat_1(sK3)),u1_struct_0(sK1))
    | spl7_5 ),
    inference(resolution,[],[f212,f100])).

fof(f212,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_relat_1(sK3))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_5
  <=> r1_tarski(u1_struct_0(sK1),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f307,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f305,f189])).

fof(f189,plain,
    ( r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f161,f180])).

fof(f180,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f179,f132])).

fof(f179,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f178,f133])).

fof(f133,plain,(
    v4_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f78,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f178,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,u1_struct_0(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f154,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f154,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_2
  <=> v1_partfun1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f305,plain,
    ( ~ r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f183,f304])).

fof(f304,plain,
    ( sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f303,f173])).

fof(f173,plain,(
    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f132,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f303,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f302,f180])).

fof(f183,plain,
    ( ~ r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f79,f180])).

fof(f256,plain,
    ( ~ spl7_11
    | spl7_12 ),
    inference(avatar_split_clause,[],[f247,f253,f249])).

fof(f247,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f172,f98])).

fof(f172,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    inference(resolution,[],[f132,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f217,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f208,f214,f210])).

fof(f208,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK3)
    | ~ r1_tarski(u1_struct_0(sK1),k2_relat_1(sK3)) ),
    inference(resolution,[],[f177,f98])).

fof(f155,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f146,f152,f148])).

fof(f146,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f145,f76])).

fof(f145,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f131,f77])).

fof(f131,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f78,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

% (11618)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (11599)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (11607)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (11597)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (11606)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (11600)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (11601)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (11596)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (11612)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (11598)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (11593)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (11615)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (11619)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (11591)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (11614)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (11611)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (11614)Refutation not found, incomplete strategy% (11614)------------------------------
% 0.22/0.54  % (11614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11614)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11614)Memory used [KB]: 10874
% 0.22/0.54  % (11614)Time elapsed: 0.099 s
% 0.22/0.54  % (11614)------------------------------
% 0.22/0.54  % (11614)------------------------------
% 0.22/0.54  % (11602)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (11603)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (11594)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (11595)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (11600)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (11617)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f479,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f155,f217,f256,f307,f310,f399,f467])).
% 0.22/0.55  fof(f467,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_6 | ~spl7_12),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f466])).
% 0.22/0.55  fof(f466,plain,(
% 0.22/0.55    $false | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f465,f443])).
% 0.22/0.55  fof(f443,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(backward_demodulation,[],[f349,f418])).
% 0.22/0.55  fof(f418,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(forward_demodulation,[],[f417,f117])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f417,plain,(
% 0.22/0.55    sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(forward_demodulation,[],[f255,f332])).
% 0.22/0.55  fof(f332,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(sK3) | (~spl7_1 | ~spl7_6)),
% 0.22/0.55    inference(resolution,[],[f316,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f316,plain,(
% 0.22/0.55    v1_xboole_0(k2_relat_1(sK3)) | (~spl7_1 | ~spl7_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f150,f216])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    u1_struct_0(sK1) = k2_relat_1(sK3) | ~spl7_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f214])).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    spl7_6 <=> u1_struct_0(sK1) = k2_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f148])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    spl7_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.55  fof(f255,plain,(
% 0.22/0.55    sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl7_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f253])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    spl7_12 <=> sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK2),k1_xboole_0,sK3,sK3) | (~spl7_1 | ~spl7_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f319,f332])).
% 0.22/0.55  fof(f319,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK3),sK3,sK3) | ~spl7_6),
% 0.22/0.55    inference(backward_demodulation,[],[f161,f216])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f160,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    (((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f50,f49,f48,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f22])).
% 0.22/0.55  fof(f22,conjecture,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) | ~v1_funct_1(sK3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f137,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f78,f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(equality_resolution,[],[f112])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f465,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(forward_demodulation,[],[f444,f458])).
% 0.22/0.55  fof(f458,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f457,f342])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl7_1 | ~spl7_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f311,f332])).
% 0.22/0.55  fof(f311,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl7_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f268,f150])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 0.22/0.55    inference(resolution,[],[f207,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.55    inference(rectify,[],[f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k2_relat_1(sK3))) )),
% 0.22/0.55    inference(resolution,[],[f177,f99])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f176,f132])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f78,f107])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | ~v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f134,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f36])).
% 0.22/0.55  % (11608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    v5_relat_1(sK3,u1_struct_0(sK1))),
% 0.22/0.55    inference(resolution,[],[f78,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f457,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,k7_relat_1(k1_xboole_0,X0)),k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(forward_demodulation,[],[f437,f418])).
% 0.22/0.55  fof(f437,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | r2_hidden(sK5(sK3,k7_relat_1(sK3,X0)),sK3)) ) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(backward_demodulation,[],[f286,f418])).
% 0.22/0.55  fof(f286,plain,(
% 0.22/0.55    ( ! [X0] : (sK3 = k7_relat_1(sK3,X0) | r2_hidden(sK5(sK3,k7_relat_1(sK3,X0)),sK3)) )),
% 0.22/0.55    inference(resolution,[],[f205,f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f63])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    ( ! [X2] : (~r1_tarski(sK3,k7_relat_1(sK3,X2)) | sK3 = k7_relat_1(sK3,X2)) )),
% 0.22/0.55    inference(resolution,[],[f171,f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 0.22/0.55    inference(resolution,[],[f132,f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.55  fof(f444,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0,k7_relat_1(k1_xboole_0,u1_struct_0(sK2))) | (~spl7_1 | ~spl7_6 | ~spl7_12)),
% 0.22/0.55    inference(backward_demodulation,[],[f351,f418])).
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK2),k1_xboole_0,sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | (~spl7_1 | ~spl7_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f328,f332])).
% 0.22/0.55  fof(f328,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK2),k2_relat_1(sK3),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~spl7_6),
% 0.22/0.55    inference(backward_demodulation,[],[f308,f216])).
% 0.22/0.55  fof(f308,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))),
% 0.22/0.55    inference(forward_demodulation,[],[f79,f302])).
% 0.22/0.55  fof(f302,plain,(
% 0.22/0.55    k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f301,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    m1_pre_topc(sK2,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f301,plain,(
% 0.22/0.55    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.55    inference(resolution,[],[f263,f127])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    m1_pre_topc(sK2,sK2)),
% 0.22/0.55    inference(resolution,[],[f126,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    l1_pre_topc(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f125,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f75,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f262,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ~v2_struct_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3) | v2_struct_0(sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f261,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    v2_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f258,f70])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK3,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.55    inference(resolution,[],[f159,f75])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k7_relat_1(sK3,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f144,f158])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ( ! [X3] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k7_relat_1(sK3,X3)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f136,f76])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X3] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k7_relat_1(sK3,X3) | ~v1_funct_1(sK3)) )),
% 0.22/0.55    inference(resolution,[],[f78,f113])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.55  % (11621)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f143,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ~v2_struct_0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f142,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    v2_pre_topc(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f141,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    l1_pre_topc(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f140,f76])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~v1_funct_1(sK3) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f130,f77])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(resolution,[],[f78,f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,axiom,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f399,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_6 | spl7_11),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f398])).
% 0.22/0.55  fof(f398,plain,(
% 0.22/0.55    $false | (~spl7_1 | ~spl7_6 | spl7_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f395,f80])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f395,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_1 | ~spl7_6 | spl7_11)),
% 0.22/0.55    inference(resolution,[],[f357,f87])).
% 0.22/0.55  fof(f357,plain,(
% 0.22/0.55    r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0) | (~spl7_1 | ~spl7_6 | spl7_11)),
% 0.22/0.55    inference(forward_demodulation,[],[f338,f117])).
% 0.22/0.55  fof(f338,plain,(
% 0.22/0.55    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3),k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) | (~spl7_1 | ~spl7_6 | spl7_11)),
% 0.22/0.55    inference(backward_demodulation,[],[f264,f332])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3),k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | spl7_11),
% 0.22/0.55    inference(resolution,[],[f251,f100])).
% 0.22/0.55  fof(f251,plain,(
% 0.22/0.55    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) | spl7_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f249])).
% 0.22/0.55  fof(f249,plain,(
% 0.22/0.55    spl7_11 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.55  fof(f310,plain,(
% 0.22/0.55    ~spl7_1 | spl7_5),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.55  fof(f309,plain,(
% 0.22/0.55    $false | (~spl7_1 | spl7_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f150,f282])).
% 0.22/0.55  fof(f282,plain,(
% 0.22/0.55    ~v1_xboole_0(u1_struct_0(sK1)) | spl7_5),
% 0.22/0.55    inference(resolution,[],[f231,f87])).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    r2_hidden(sK5(u1_struct_0(sK1),k2_relat_1(sK3)),u1_struct_0(sK1)) | spl7_5),
% 0.22/0.55    inference(resolution,[],[f212,f100])).
% 0.22/0.55  fof(f212,plain,(
% 0.22/0.55    ~r1_tarski(u1_struct_0(sK1),k2_relat_1(sK3)) | spl7_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f210])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    spl7_5 <=> r1_tarski(u1_struct_0(sK1),k2_relat_1(sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.55  fof(f307,plain,(
% 0.22/0.55    ~spl7_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f306])).
% 0.22/0.55  fof(f306,plain,(
% 0.22/0.55    $false | ~spl7_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f305,f189])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3) | ~spl7_2),
% 0.22/0.55    inference(backward_demodulation,[],[f161,f180])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    u1_struct_0(sK2) = k1_relat_1(sK3) | ~spl7_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f179,f132])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    u1_struct_0(sK2) = k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl7_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f178,f133])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    v4_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.55    inference(resolution,[],[f78,f108])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    u1_struct_0(sK2) = k1_relat_1(sK3) | ~v4_relat_1(sK3,u1_struct_0(sK2)) | ~v1_relat_1(sK3) | ~spl7_2),
% 0.22/0.55    inference(resolution,[],[f154,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    v1_partfun1(sK3,u1_struct_0(sK2)) | ~spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f152])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    spl7_2 <=> v1_partfun1(sK3,u1_struct_0(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.55  fof(f305,plain,(
% 0.22/0.55    ~r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3) | ~spl7_2),
% 0.22/0.55    inference(backward_demodulation,[],[f183,f304])).
% 0.22/0.55  fof(f304,plain,(
% 0.22/0.55    sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3) | ~spl7_2),
% 0.22/0.55    inference(forward_demodulation,[],[f303,f173])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    sK3 = k7_relat_1(sK3,k1_relat_1(sK3))),
% 0.22/0.55    inference(resolution,[],[f132,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.55  fof(f303,plain,(
% 0.22/0.55    k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,k1_relat_1(sK3)) | ~spl7_2),
% 0.22/0.55    inference(forward_demodulation,[],[f302,f180])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    ~r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) | ~spl7_2),
% 0.22/0.55    inference(backward_demodulation,[],[f79,f180])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    ~spl7_11 | spl7_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f247,f253,f249])).
% 0.22/0.55  fof(f247,plain,(
% 0.22/0.55    sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)),
% 0.22/0.55    inference(resolution,[],[f172,f98])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 0.22/0.55    inference(resolution,[],[f132,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    ~spl7_5 | spl7_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f208,f214,f210])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    u1_struct_0(sK1) = k2_relat_1(sK3) | ~r1_tarski(u1_struct_0(sK1),k2_relat_1(sK3))),
% 0.22/0.55    inference(resolution,[],[f177,f98])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    spl7_1 | spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f146,f152,f148])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    v1_partfun1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f145,f76])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f77])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.55    inference(resolution,[],[f78,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(flattening,[],[f33])).
% 0.22/0.55  % (11618)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11600)------------------------------
% 0.22/0.55  % (11600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11600)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11600)Memory used [KB]: 11001
% 0.22/0.55  % (11600)Time elapsed: 0.125 s
% 0.22/0.55  % (11600)------------------------------
% 0.22/0.55  % (11600)------------------------------
% 0.22/0.55  % (11620)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (11616)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (11590)Success in time 0.19 s
%------------------------------------------------------------------------------
