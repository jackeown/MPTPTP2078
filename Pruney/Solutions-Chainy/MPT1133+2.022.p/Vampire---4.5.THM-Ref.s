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
% DateTime   : Thu Dec  3 13:09:31 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  663 (12401 expanded)
%              Number of leaves         :   57 (4202 expanded)
%              Depth                    :   41
%              Number of atoms          : 4023 (131558 expanded)
%              Number of equality atoms :  129 (11105 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f152,f190,f199,f202,f254,f311,f322,f353,f476,f837,f839,f891,f947,f1139,f1187,f1190,f1204,f1206,f1210,f1361,f1915,f2196,f2200,f2253,f2583,f2588,f2821,f3027,f3632,f3674,f3942,f4081,f4459,f4933,f5197,f5491,f6308])).

fof(f6308,plain,
    ( spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(avatar_contradiction_clause,[],[f6307])).

fof(f6307,plain,
    ( $false
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6306,f2199])).

fof(f2199,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f2198])).

fof(f2198,plain,
    ( spl6_62
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f6306,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(forward_demodulation,[],[f6305,f4847])).

fof(f4847,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f4846,f1572])).

fof(f1572,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(resolution,[],[f1386,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1386,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f329,f1371])).

fof(f1371,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(resolution,[],[f198,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f198,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f329,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f328,f175])).

fof(f175,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f124])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f60,f59,f58,f57])).

fof(f57,plain,
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

fof(f58,plain,
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

fof(f59,plain,
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

fof(f60,plain,
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

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f328,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f155])).

fof(f155,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f84,f87])).

fof(f87,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f61])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f211,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f211,plain,(
    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f210,f175])).

fof(f210,plain,
    ( r1_tarski(k2_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f174,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f174,plain,(
    v5_relat_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f83,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f4846,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f4845,f2231])).

fof(f2231,plain,
    ( v4_relat_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f173,f1371])).

fof(f173,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4845,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_64 ),
    inference(resolution,[],[f2246,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f2246,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f2244,plain,
    ( spl6_64
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f6305,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6304,f2195])).

fof(f2195,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f2194,plain,
    ( spl6_61
  <=> ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f6304,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(forward_demodulation,[],[f6303,f4847])).

fof(f6303,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6302,f2199])).

fof(f6302,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(forward_demodulation,[],[f6301,f4847])).

fof(f6301,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6300,f2195])).

fof(f6300,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(forward_demodulation,[],[f6299,f4847])).

fof(f6299,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6298,f77])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f6298,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6297,f78])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f6297,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6296,f1374])).

fof(f1374,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f155,f1371])).

fof(f6296,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6295,f5538])).

fof(f5538,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f146,f1371])).

fof(f146,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f6295,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(resolution,[],[f6286,f5005])).

fof(f5005,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | v5_pre_topc(X0,X1,sK1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f5004,f79])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f5004,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X0,X1,sK1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f4991,f80])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f4991,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X0,X1,sK1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl6_16 ),
    inference(superposition,[],[f137,f321])).

fof(f321,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_16
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f137,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
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
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f6286,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6285,f2199])).

fof(f6285,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6284,f1374])).

fof(f6284,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6278,f4823])).

fof(f4823,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f4502,f321])).

fof(f4502,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_8
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f1149,f1371])).

fof(f1149,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f1148])).

fof(f1148,plain,
    ( spl6_49
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f6278,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6277,f4905])).

fof(f4905,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f4796,f4847])).

fof(f4796,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f4505,f321])).

fof(f4505,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f153,f1371])).

fof(f153,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f86,f87])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f61])).

% (30837)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
fof(f6277,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f6274,f5214])).

fof(f5214,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(backward_demodulation,[],[f4936,f5208])).

fof(f5208,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f5203,f91])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f5203,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(resolution,[],[f5200,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5200,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f5199,f321])).

fof(f5199,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f926,f1371])).

fof(f926,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f925])).

fof(f925,plain,
    ( spl6_31
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f4936,plain,
    ( m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(forward_demodulation,[],[f3389,f4847])).

fof(f3389,plain,
    ( m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl6_101 ),
    inference(avatar_component_clause,[],[f3388])).

fof(f3388,plain,
    ( spl6_101
  <=> m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f6274,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_64 ),
    inference(resolution,[],[f5535,f5216])).

fof(f5216,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f5144,f5208])).

fof(f5144,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f5143,f77])).

fof(f5143,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f5141,f78])).

fof(f5141,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(superposition,[],[f5025,f4847])).

fof(f5025,plain,
    ( ! [X19,X18] :
        ( ~ v5_pre_topc(X18,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0)))
        | v5_pre_topc(X18,X19,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X18,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),k1_xboole_0)))
        | ~ v1_funct_2(X18,u1_struct_0(X19),k1_xboole_0)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19) )
    | ~ spl6_16
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f5024,f1098])).

fof(f1098,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1097,plain,
    ( spl6_46
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f5024,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0)))
        | ~ v5_pre_topc(X18,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X18,X19,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X18,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),k1_xboole_0)))
        | ~ v1_funct_2(X18,u1_struct_0(X19),k1_xboole_0)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19) )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f5001,f637])).

fof(f637,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f158,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f158,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f80,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f5001,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0)))
        | ~ v5_pre_topc(X18,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X18,X19,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X18,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),k1_xboole_0)))
        | ~ v1_funct_2(X18,u1_struct_0(X19),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19) )
    | ~ spl6_16 ),
    inference(superposition,[],[f139,f321])).

fof(f139,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
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
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f5535,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_8
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f1124,f1371])).

fof(f1124,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1122,plain,
    ( spl6_48
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f5491,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(avatar_contradiction_clause,[],[f5490])).

fof(f5490,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5489,f2199])).

fof(f5489,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5488,f1374])).

fof(f5488,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_49
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5487,f4823])).

fof(f5487,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5486,f4904])).

fof(f4904,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_8
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f4500,f4847])).

fof(f4500,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f150,f1372])).

fof(f1372,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f87,f1371])).

fof(f150,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f5486,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5485,f5388])).

fof(f5388,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5387,f2199])).

fof(f5387,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5386,f1374])).

fof(f5386,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5349,f2199])).

fof(f5349,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_61
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5348,f3828])).

fof(f3828,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f145,f1371])).

fof(f145,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f5348,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_61
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5346,f5214])).

fof(f5346,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(resolution,[],[f5215,f2195])).

fof(f5215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,sK0,sK1)
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f5090,f5208])).

fof(f5090,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X0,sK0,sK1)
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f5089,f77])).

fof(f5089,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X0,sK0,sK1)
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f5081,f78])).

fof(f5081,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X0,sK0,sK1)
        | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_64 ),
    inference(superposition,[],[f5007,f4847])).

fof(f5007,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f5006,f79])).

fof(f5006,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f4992,f80])).

fof(f4992,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_16 ),
    inference(superposition,[],[f138,f321])).

fof(f138,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
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
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f5485,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5483,f5214])).

fof(f5483,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(resolution,[],[f5217,f4905])).

fof(f5217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_31
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f5160,f5208])).

fof(f5160,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f5159,f77])).

fof(f5159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f5150,f78])).

fof(f5150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)))
        | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_46
    | ~ spl6_64 ),
    inference(superposition,[],[f5029,f4847])).

fof(f5029,plain,
    ( ! [X23,X22] :
        ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0)))
        | ~ v5_pre_topc(X22,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X22,u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),k1_xboole_0)))
        | ~ v1_funct_2(X22,u1_struct_0(X23),k1_xboole_0)
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X23) )
    | ~ spl6_16
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f5028,f1098])).

fof(f5028,plain,
    ( ! [X23,X22] :
        ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0)))
        | ~ v5_pre_topc(X22,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X22,u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),k1_xboole_0)))
        | ~ v1_funct_2(X22,u1_struct_0(X23),k1_xboole_0)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X23) )
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f5003,f637])).

fof(f5003,plain,
    ( ! [X23,X22] :
        ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0)))
        | ~ v5_pre_topc(X22,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X22,u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),k1_xboole_0)))
        | ~ v1_funct_2(X22,u1_struct_0(X23),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X23) )
    | ~ spl6_16 ),
    inference(superposition,[],[f140,f321])).

fof(f140,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f5197,plain,
    ( ~ spl6_8
    | ~ spl6_16
    | spl6_31
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(avatar_contradiction_clause,[],[f5196])).

fof(f5196,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_16
    | spl6_31
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5195,f90])).

fof(f90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f5195,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | spl6_31
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f5191,f4801])).

fof(f4801,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_16
    | spl6_31 ),
    inference(forward_demodulation,[],[f1444,f321])).

fof(f1444,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl6_8
    | spl6_31 ),
    inference(backward_demodulation,[],[f1042,f1371])).

fof(f1042,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl6_31 ),
    inference(resolution,[],[f994,f102])).

fof(f102,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f65,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f994,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl6_31 ),
    inference(resolution,[],[f927,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f73,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f927,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f925])).

fof(f5191,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_64
    | ~ spl6_101 ),
    inference(resolution,[],[f4936,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f4933,plain,
    ( ~ spl6_8
    | ~ spl6_64
    | spl6_101 ),
    inference(avatar_contradiction_clause,[],[f4932])).

fof(f4932,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_64
    | spl6_101 ),
    inference(subsumption_resolution,[],[f4894,f135])).

fof(f135,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f4894,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_64
    | spl6_101 ),
    inference(backward_demodulation,[],[f3470,f4847])).

fof(f3470,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | spl6_101 ),
    inference(resolution,[],[f3390,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3390,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | spl6_101 ),
    inference(avatar_component_clause,[],[f3388])).

fof(f4459,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(avatar_contradiction_clause,[],[f4458])).

fof(f4458,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4457,f2385])).

fof(f2385,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1387,f189])).

fof(f189,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_6
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1387,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f331,f1371])).

fof(f331,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f330,f175])).

fof(f330,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f240,f155])).

fof(f240,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f211,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4457,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4456,f2386])).

fof(f2386,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1386,f189])).

fof(f4456,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4455,f1374])).

fof(f4455,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4454,f2652])).

fof(f2652,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f2651,f1572])).

fof(f2651,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f2650,f1374])).

fof(f2650,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f2647,f91])).

fof(f2647,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(superposition,[],[f111,f2416])).

fof(f2416,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f2271,f189])).

fof(f2271,plain,
    ( u1_struct_0(sK1) = k2_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f253,f1371])).

fof(f253,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_11
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f4454,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4453,f3827])).

fof(f3827,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f3826,f1372])).

fof(f3826,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f150,f189])).

fof(f4453,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4451,f4337])).

fof(f4337,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4336,f2374])).

fof(f2374,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2237,f189])).

fof(f2237,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f82,f1371])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f4336,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4335,f2386])).

fof(f4335,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4334,f1374])).

fof(f4334,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4333,f2385])).

fof(f4333,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4331,f3828])).

fof(f4331,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(resolution,[],[f4191,f2375])).

fof(f2375,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2236,f189])).

fof(f2236,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f83,f1371])).

fof(f4191,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
        | ~ v5_pre_topc(X11,sK0,sK1)
        | v5_pre_topc(X11,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(X11,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X11,u1_struct_0(sK0),k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4190,f77])).

fof(f4190,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v5_pre_topc(X11,sK0,sK1)
        | v5_pre_topc(X11,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(X11,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
        | ~ v1_funct_2(X11,u1_struct_0(sK0),k1_xboole_0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4154,f78])).

fof(f4154,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v5_pre_topc(X11,sK0,sK1)
        | v5_pre_topc(X11,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(X11,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
        | ~ v1_funct_2(X11,u1_struct_0(sK0),k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(superposition,[],[f2637,f4133])).

fof(f4133,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4132,f1572])).

fof(f4132,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4131,f2665])).

fof(f2665,plain,
    ( v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f2597,f125])).

fof(f2597,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2596,f1371])).

fof(f2596,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f153,f189])).

fof(f4131,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_117 ),
    inference(resolution,[],[f3662,f113])).

fof(f3662,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_117 ),
    inference(avatar_component_clause,[],[f3660])).

fof(f3660,plain,
    ( spl6_117
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f2637,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0)))
        | ~ v5_pre_topc(X14,X15,sK1)
        | v5_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)),sK1)
        | ~ v1_funct_2(X14,u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0)
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f2636,f79])).

fof(f2636,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0)))
        | ~ v5_pre_topc(X14,X15,sK1)
        | v5_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)),sK1)
        | ~ v1_funct_2(X14,u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0)
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f2621,f80])).

fof(f2621,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0)))
        | ~ v5_pre_topc(X14,X15,sK1)
        | v5_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)),sK1)
        | ~ v1_funct_2(X14,u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0)
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl6_6 ),
    inference(superposition,[],[f140,f189])).

fof(f4451,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(resolution,[],[f4245,f2655])).

fof(f2655,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f2654,f1572])).

fof(f2654,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f2653,f1374])).

fof(f2653,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f2648,f91])).

fof(f2648,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(superposition,[],[f112,f2416])).

fof(f4245,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_68
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4244,f2771])).

fof(f2771,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f2770])).

fof(f2770,plain,
    ( spl6_68
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f4244,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(subsumption_resolution,[],[f4237,f159])).

fof(f159,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f157,f109])).

fof(f157,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f78,f94])).

fof(f4237,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_117 ),
    inference(superposition,[],[f2629,f4133])).

fof(f2629,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f2628,f79])).

fof(f2628,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f2617,f80])).

fof(f2617,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6 ),
    inference(superposition,[],[f138,f189])).

fof(f4081,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_55
    | ~ spl6_118 ),
    inference(avatar_contradiction_clause,[],[f4080])).

fof(f4080,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_55
    | ~ spl6_118 ),
    inference(subsumption_resolution,[],[f4079,f3669])).

fof(f3669,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_118 ),
    inference(avatar_component_clause,[],[f3667])).

fof(f3667,plain,
    ( spl6_118
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f4079,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_55 ),
    inference(forward_demodulation,[],[f4078,f189])).

fof(f4078,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_55 ),
    inference(forward_demodulation,[],[f1679,f2416])).

fof(f1679,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k2_relat_1(k1_xboole_0)
    | spl6_55 ),
    inference(avatar_component_clause,[],[f1678])).

fof(f1678,plain,
    ( spl6_55
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f3942,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(avatar_contradiction_clause,[],[f3941])).

fof(f3941,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3940,f77])).

fof(f3940,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3939,f78])).

fof(f3939,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3938,f1374])).

fof(f3938,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3937,f3848])).

fof(f3848,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3847,f2374])).

fof(f3847,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f3846,f3685])).

fof(f3685,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f3684,f189])).

fof(f3684,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f1680,f2416])).

fof(f1680,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0)
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f1678])).

fof(f3846,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3845,f2375])).

fof(f3845,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f3844,f3685])).

fof(f3844,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3843,f3705])).

fof(f3705,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(backward_demodulation,[],[f2599,f3685])).

fof(f2599,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2598,f1371])).

fof(f2598,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f154,f189])).

fof(f154,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f85,f87])).

fof(f85,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f3843,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_46
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f3842,f3685])).

fof(f3842,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3841,f77])).

fof(f3841,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3840,f78])).

fof(f3840,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3839,f2390])).

fof(f2390,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f1098,f189])).

fof(f3839,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f3838,f454])).

fof(f454,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl6_17
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f3838,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f3837,f1374])).

fof(f3837,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2662,f3827])).

fof(f2662,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f2597,f140])).

fof(f3937,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3936,f3828])).

fof(f3936,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f3930,f2374])).

fof(f3930,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(resolution,[],[f3779,f2375])).

fof(f3779,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_1(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(duplicate_literal_removal,[],[f3778])).

fof(f3778,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f3773,f3685])).

fof(f3773,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(duplicate_literal_removal,[],[f3707])).

fof(f3707,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,sK1)
        | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(backward_demodulation,[],[f2629,f3685])).

fof(f3674,plain,
    ( spl6_117
    | spl6_118
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f3673,f196,f187,f3667,f3660])).

fof(f3673,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f3672,f1374])).

fof(f3672,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2664,f2599])).

fof(f2664,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f2597,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f3632,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f3631])).

fof(f3631,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3630,f2374])).

fof(f3630,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f3629,f189])).

fof(f3629,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3628,f2375])).

fof(f3628,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f3627,f189])).

fof(f3627,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3626,f79])).

fof(f3626,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3625,f80])).

fof(f3625,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3624,f1374])).

fof(f3624,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3623,f2652])).

fof(f3623,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3622,f1373])).

fof(f1373,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f146,f1371])).

fof(f3622,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3614,f2655])).

fof(f3614,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(resolution,[],[f3612,f3154])).

fof(f3154,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3153,f77])).

fof(f3153,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X3)
        | v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3139,f78])).

fof(f3139,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X3)
        | v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(superposition,[],[f139,f3132])).

fof(f3132,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3131,f1572])).

fof(f3131,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3130,f2665])).

fof(f3130,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(resolution,[],[f3095,f113])).

fof(f3095,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3094,f1374])).

fof(f3094,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3093,f2599])).

fof(f3093,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f2664,f3090])).

fof(f3090,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | spl6_16 ),
    inference(forward_demodulation,[],[f320,f189])).

fof(f320,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f319])).

fof(f3612,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3611,f2385])).

fof(f3611,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3610,f2386])).

fof(f3610,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3609,f1374])).

fof(f3609,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3608,f2652])).

fof(f3608,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3607,f2655])).

fof(f3607,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16
    | ~ spl6_68 ),
    inference(resolution,[],[f3186,f2376])).

fof(f2376,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2218,f189])).

fof(f2218,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f149,f1372])).

fof(f149,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f3186,plain,
    ( ! [X2] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3185,f2771])).

fof(f3185,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f3176,f159])).

fof(f3176,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
        | ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl6_6
    | ~ spl6_8
    | spl6_16 ),
    inference(superposition,[],[f2625,f3132])).

fof(f2625,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f2624,f79])).

fof(f2624,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f2615,f80])).

fof(f2615,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6 ),
    inference(superposition,[],[f137,f189])).

fof(f3027,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f3026])).

fof(f3026,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3025,f77])).

fof(f3025,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3024,f78])).

fof(f3024,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3023,f1374])).

fof(f3023,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3022,f1373])).

fof(f3022,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3021,f2374])).

fof(f3021,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3015,f2375])).

fof(f3015,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(resolution,[],[f2871,f2900])).

fof(f2900,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2899,f2374])).

fof(f2899,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f2898,f2831])).

fof(f2831,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f2830,f189])).

fof(f2830,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f2829,f2416])).

fof(f2829,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f946,f1371])).

fof(f946,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(sK2)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f944])).

fof(f944,plain,
    ( spl6_34
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f2898,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2897,f2375])).

fof(f2897,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f2896,f2831])).

fof(f2896,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2895,f2858])).

fof(f2858,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f2599,f2831])).

fof(f2895,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f2894,f2831])).

fof(f2894,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2893,f77])).

fof(f2893,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2892,f78])).

fof(f2892,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2891,f2390])).

fof(f2891,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f2890,f454])).

fof(f2890,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2889,f1374])).

fof(f2889,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2663,f2376])).

fof(f2663,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f2597,f139])).

fof(f2871,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(duplicate_literal_removal,[],[f2870])).

fof(f2870,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f2866,f2831])).

fof(f2866,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(duplicate_literal_removal,[],[f2859])).

fof(f2859,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f2625,f2831])).

fof(f2821,plain,(
    spl6_68 ),
    inference(avatar_contradiction_clause,[],[f2820])).

fof(f2820,plain,
    ( $false
    | spl6_68 ),
    inference(subsumption_resolution,[],[f2819,f77])).

fof(f2819,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_68 ),
    inference(subsumption_resolution,[],[f2818,f78])).

fof(f2818,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_68 ),
    inference(resolution,[],[f2772,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f2772,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_68 ),
    inference(avatar_component_clause,[],[f2770])).

fof(f2588,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_16
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f2587])).

fof(f2587,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_16
    | spl6_34 ),
    inference(subsumption_resolution,[],[f2586,f2404])).

fof(f2404,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f321,f189])).

fof(f2586,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_34 ),
    inference(forward_demodulation,[],[f2585,f189])).

fof(f2585,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_34 ),
    inference(forward_demodulation,[],[f2584,f2416])).

fof(f2584,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k2_relat_1(k1_xboole_0)
    | ~ spl6_8
    | spl6_34 ),
    inference(forward_demodulation,[],[f945,f1371])).

fof(f945,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k2_relat_1(sK2)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f944])).

fof(f2583,plain,
    ( ~ spl6_8
    | spl6_57 ),
    inference(avatar_contradiction_clause,[],[f2582])).

fof(f2582,plain,
    ( $false
    | ~ spl6_8
    | spl6_57 ),
    inference(subsumption_resolution,[],[f2179,f1572])).

fof(f2179,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_57 ),
    inference(avatar_component_clause,[],[f2177])).

fof(f2177,plain,
    ( spl6_57
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f2253,plain,
    ( spl6_6
    | spl6_64
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f2252,f196,f2244,f187])).

fof(f2252,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2251,f1374])).

fof(f2251,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2250,f1371])).

fof(f2250,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2249,f2237])).

fof(f2249,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2248,f1371])).

fof(f2248,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f707,f1371])).

fof(f707,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f83,f142])).

fof(f2200,plain,
    ( ~ spl6_57
    | spl6_62
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f2023,f944,f319,f196,f2198,f2177])).

fof(f2023,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f2022,f1374])).

fof(f2022,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f2019,f91])).

fof(f2019,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(superposition,[],[f111,f1923])).

fof(f1923,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f1709,f321])).

fof(f1709,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f946,f1371])).

fof(f2196,plain,
    ( ~ spl6_57
    | spl6_61
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f2026,f944,f319,f196,f2194,f2177])).

fof(f2026,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f2025,f1374])).

fof(f2025,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f2020,f91])).

fof(f2020,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(superposition,[],[f112,f1923])).

fof(f1915,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f1914])).

fof(f1914,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1913,f79])).

fof(f1913,plain,
    ( ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1912,f80])).

fof(f1912,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1911,f1374])).

fof(f1911,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1910,f1373])).

fof(f1910,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1909,f1387])).

fof(f1909,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1899,f1386])).

fof(f1899,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | spl6_16
    | ~ spl6_19 ),
    inference(resolution,[],[f1786,f1385])).

fof(f1385,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f310,f1371])).

fof(f310,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_14
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1786,plain,
    ( ! [X8,X9] :
        ( ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9))
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16
    | ~ spl6_19 ),
    inference(duplicate_literal_removal,[],[f1785])).

fof(f1785,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f1778,f1764])).

fof(f1764,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f1763,f953])).

fof(f953,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(resolution,[],[f892,f124])).

fof(f892,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f462,f717])).

fof(f717,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f716,f175])).

fof(f716,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f715,f173])).

fof(f715,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f185,f113])).

fof(f185,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_5
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f462,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl6_19
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f1763,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f1762,f1401])).

fof(f1401,plain,
    ( v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))))
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f747,f1371])).

fof(f747,plain,
    ( v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl6_5 ),
    inference(resolution,[],[f720,f125])).

fof(f720,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f153,f717])).

fof(f1762,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(resolution,[],[f1691,f113])).

fof(f1691,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))))
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f1690,f1374])).

fof(f1690,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f1689,f1390])).

fof(f1390,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f721,f1371])).

fof(f721,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f154,f717])).

fof(f1689,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f1514,f320])).

fof(f1514,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f1389,f142])).

fof(f1389,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f720,f1371])).

fof(f1778,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9))
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16
    | ~ spl6_19 ),
    inference(duplicate_literal_removal,[],[f1771])).

fof(f1771,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8
    | spl6_16
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f1472,f1764])).

fof(f1472,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1471,f1371])).

fof(f1471,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1470,f1371])).

fof(f1470,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1469,f1371])).

fof(f1469,plain,
    ( ! [X8,X9] :
        ( ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f1409,f1371])).

fof(f1409,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f776,f1371])).

fof(f776,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f775,f77])).

fof(f775,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f761,f78])).

fof(f761,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_5 ),
    inference(superposition,[],[f139,f717])).

fof(f1361,plain,
    ( spl6_1
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f1360])).

fof(f1360,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1359,f79])).

fof(f1359,plain,
    ( ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1358,f80])).

fof(f1358,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1357,f155])).

fof(f1357,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_1
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1356,f146])).

fof(f1356,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1355,f331])).

fof(f1355,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1347,f329])).

fof(f1347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | spl6_8
    | ~ spl6_14 ),
    inference(resolution,[],[f1248,f310])).

fof(f1248,plain,
    ( ! [X8,X9] :
        ( ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | spl6_8 ),
    inference(duplicate_literal_removal,[],[f1247])).

fof(f1247,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | spl6_8 ),
    inference(forward_demodulation,[],[f1240,f1225])).

fof(f1225,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5
    | spl6_8 ),
    inference(subsumption_resolution,[],[f1224,f175])).

fof(f1224,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5
    | spl6_8 ),
    inference(subsumption_resolution,[],[f1223,f747])).

fof(f1223,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5
    | spl6_8 ),
    inference(resolution,[],[f1158,f113])).

fof(f1158,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl6_5
    | spl6_8 ),
    inference(subsumption_resolution,[],[f1157,f754])).

fof(f754,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5
    | spl6_8 ),
    inference(subsumption_resolution,[],[f750,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f196])).

fof(f750,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(resolution,[],[f720,f108])).

fof(f1157,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f1156,f155])).

fof(f1156,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f751,f721])).

fof(f751,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(resolution,[],[f720,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f1240,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | spl6_8 ),
    inference(duplicate_literal_removal,[],[f1235])).

fof(f1235,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9)
        | v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl6_5
    | spl6_8 ),
    inference(backward_demodulation,[],[f776,f1225])).

fof(f1210,plain,(
    spl6_46 ),
    inference(avatar_contradiction_clause,[],[f1209])).

fof(f1209,plain,
    ( $false
    | spl6_46 ),
    inference(subsumption_resolution,[],[f1208,f79])).

fof(f1208,plain,
    ( ~ v2_pre_topc(sK1)
    | spl6_46 ),
    inference(subsumption_resolution,[],[f1207,f80])).

fof(f1207,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_46 ),
    inference(resolution,[],[f1099,f97])).

fof(f1099,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_46 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1206,plain,
    ( ~ spl6_5
    | spl6_49 ),
    inference(avatar_contradiction_clause,[],[f1205])).

fof(f1205,plain,
    ( $false
    | ~ spl6_5
    | spl6_49 ),
    inference(subsumption_resolution,[],[f721,f1150])).

fof(f1150,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_49 ),
    inference(avatar_component_clause,[],[f1148])).

fof(f1204,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | spl6_48 ),
    inference(avatar_contradiction_clause,[],[f1203])).

fof(f1203,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5
    | spl6_48 ),
    inference(subsumption_resolution,[],[f1202,f1123])).

fof(f1123,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_48 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1202,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1201,f87])).

fof(f1201,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f149,f717])).

fof(f1190,plain,
    ( ~ spl6_5
    | spl6_8
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f1189])).

fof(f1189,plain,
    ( $false
    | ~ spl6_5
    | spl6_8
    | spl6_15 ),
    inference(subsumption_resolution,[],[f316,f1158])).

fof(f316,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl6_15
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1187,plain,
    ( ~ spl6_16
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f1186])).

fof(f1186,plain,
    ( $false
    | ~ spl6_16
    | spl6_33 ),
    inference(subsumption_resolution,[],[f1172,f91])).

fof(f1172,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl6_16
    | spl6_33 ),
    inference(backward_demodulation,[],[f942,f321])).

fof(f942,plain,
    ( ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_relat_1(sK2))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f940])).

fof(f940,plain,
    ( spl6_33
  <=> r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1139,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f1138])).

fof(f1138,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1137,f331])).

fof(f1137,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f1136,f818])).

fof(f818,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f817,f175])).

fof(f817,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f816,f747])).

fof(f816,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_relat_1(sK2)
    | ~ spl6_15 ),
    inference(resolution,[],[f317,f113])).

fof(f317,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f315])).

fof(f1136,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1135,f329])).

fof(f1135,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f1134,f818])).

fof(f1134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1133,f823])).

fof(f823,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f721,f818])).

fof(f1133,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f1132,f818])).

fof(f1132,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1131,f766])).

fof(f766,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f765,f77])).

fof(f765,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f756,f78])).

fof(f756,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(superposition,[],[f97,f717])).

fof(f1131,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1130,f724])).

fof(f724,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f159,f717])).

fof(f1130,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1129,f79])).

fof(f1129,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1128,f80])).

fof(f1128,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1127,f155])).

fof(f1127,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1126,f863])).

fof(f863,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f862,f87])).

fof(f862,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f150,f717])).

fof(f1126,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f744,f1118])).

fof(f1118,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1117,f79])).

fof(f1117,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1116,f80])).

fof(f1116,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1106,f155])).

fof(f1106,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1105,f145])).

fof(f1105,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f1085,f331])).

fof(f1085,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(resolution,[],[f847,f329])).

fof(f847,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_1(X12)
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(duplicate_literal_removal,[],[f846])).

fof(f846,plain,
    ( ! [X12,X13] :
        ( ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f832,f818])).

fof(f832,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(duplicate_literal_removal,[],[f830])).

fof(f830,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f780,f818])).

fof(f780,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f779,f77])).

fof(f779,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f763,f78])).

fof(f763,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))))
        | ~ v5_pre_topc(X12,sK0,X13)
        | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_5 ),
    inference(superposition,[],[f140,f717])).

fof(f744,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f720,f138])).

fof(f947,plain,
    ( ~ spl6_33
    | spl6_34
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f938,f183,f944,f940])).

fof(f938,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(sK2)
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_relat_1(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f874,f117])).

fof(f874,plain,
    ( r1_tarski(k2_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f873,f175])).

fof(f873,plain,
    ( r1_tarski(k2_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f748,f106])).

fof(f748,plain,
    ( v5_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(resolution,[],[f720,f126])).

fof(f891,plain,
    ( ~ spl6_5
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f890])).

fof(f890,plain,
    ( $false
    | ~ spl6_5
    | spl6_19 ),
    inference(subsumption_resolution,[],[f889,f91])).

fof(f889,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | ~ spl6_5
    | spl6_19 ),
    inference(resolution,[],[f733,f122])).

fof(f733,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_5
    | spl6_19 ),
    inference(backward_demodulation,[],[f463,f717])).

fof(f463,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f461])).

fof(f839,plain,
    ( ~ spl6_5
    | spl6_13
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f838])).

fof(f838,plain,
    ( $false
    | ~ spl6_5
    | spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f820,f329])).

fof(f820,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_5
    | spl6_13
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f306,f818])).

fof(f306,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f837,plain,
    ( ~ spl6_5
    | spl6_12
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f836])).

fof(f836,plain,
    ( $false
    | ~ spl6_5
    | spl6_12
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f819,f331])).

fof(f819,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_5
    | spl6_12
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f302,f818])).

fof(f302,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl6_12
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f476,plain,
    ( ~ spl6_6
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl6_6
    | spl6_17 ),
    inference(subsumption_resolution,[],[f472,f455])).

fof(f455,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f453])).

fof(f472,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f337,f109])).

fof(f337,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f158,f189])).

fof(f353,plain,
    ( ~ spl6_6
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl6_6
    | spl6_10 ),
    inference(subsumption_resolution,[],[f345,f91])).

fof(f345,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl6_6
    | spl6_10 ),
    inference(backward_demodulation,[],[f249,f189])).

fof(f249,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_relat_1(sK2))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl6_10
  <=> r1_tarski(u1_struct_0(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f322,plain,
    ( spl6_15
    | spl6_16
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f313,f183,f319,f315])).

fof(f313,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f312,f155])).

fof(f312,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f284,f218])).

fof(f218,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f154,f214])).

fof(f214,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f213,f175])).

fof(f213,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f212,f173])).

fof(f212,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f185,f113])).

fof(f284,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f217,f142])).

fof(f217,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f153,f214])).

fof(f311,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f298,f183,f148,f308,f304,f300])).

fof(f298,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f297,f265])).

fof(f265,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f264,f77])).

fof(f264,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f255,f78])).

fof(f255,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(superposition,[],[f97,f214])).

fof(f297,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f296,f221])).

fof(f221,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f159,f214])).

fof(f296,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f295,f79])).

fof(f295,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f294,f80])).

fof(f294,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f293,f155])).

fof(f293,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f292,f218])).

fof(f292,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f283,f219])).

fof(f219,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f156,f214])).

fof(f156,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f149,f87])).

fof(f283,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f217,f137])).

fof(f254,plain,
    ( ~ spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f245,f251,f247])).

fof(f245,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ r1_tarski(u1_struct_0(sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f211,f117])).

fof(f202,plain,
    ( spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f201,f183,f192])).

fof(f192,plain,
    ( spl6_7
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f201,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f200,f155])).

fof(f200,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f177,f82])).

fof(f177,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f83,f105])).

fof(f199,plain,
    ( ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f176,f196,f192])).

fof(f176,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f83,f108])).

fof(f190,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f181,f187,f183])).

fof(f181,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f180,f155])).

fof(f180,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f172,f82])).

fof(f172,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f83,f142])).

fof(f152,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f88,f148,f144])).

fof(f88,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f151,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f89,f148,f144])).

fof(f89,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (30796)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (30781)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (30773)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (30795)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (30774)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (30796)Refutation not found, incomplete strategy% (30796)------------------------------
% 0.22/0.56  % (30796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (30796)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (30796)Memory used [KB]: 11001
% 0.22/0.56  % (30796)Time elapsed: 0.139 s
% 0.22/0.56  % (30796)------------------------------
% 0.22/0.56  % (30796)------------------------------
% 0.22/0.56  % (30801)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (30789)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (30785)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (30778)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (30777)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (30798)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (30773)Refutation not found, incomplete strategy% (30773)------------------------------
% 0.22/0.57  % (30773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (30784)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (30773)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (30773)Memory used [KB]: 2046
% 0.22/0.58  % (30773)Time elapsed: 0.148 s
% 0.22/0.58  % (30773)------------------------------
% 0.22/0.58  % (30773)------------------------------
% 0.22/0.58  % (30800)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.59  % (30791)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.59  % (30775)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (30784)Refutation not found, incomplete strategy% (30784)------------------------------
% 0.22/0.60  % (30784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (30784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (30784)Memory used [KB]: 10874
% 0.22/0.60  % (30784)Time elapsed: 0.185 s
% 0.22/0.60  % (30779)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.60  % (30784)------------------------------
% 0.22/0.60  % (30784)------------------------------
% 0.22/0.60  % (30794)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.60  % (30783)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.62  % (30803)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.62  % (30802)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.62  % (30776)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.89/0.63  % (30788)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.89/0.63  % (30783)Refutation not found, incomplete strategy% (30783)------------------------------
% 1.89/0.63  % (30783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.63  % (30783)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.63  
% 1.89/0.63  % (30783)Memory used [KB]: 10874
% 1.89/0.63  % (30783)Time elapsed: 0.208 s
% 1.89/0.63  % (30783)------------------------------
% 1.89/0.63  % (30783)------------------------------
% 1.89/0.63  % (30787)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.89/0.64  % (30797)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.89/0.64  % (30799)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.89/0.64  % (30782)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.89/0.64  % (30793)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.89/0.64  % (30790)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.89/0.64  % (30780)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.89/0.64  % (30786)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.19/0.66  % (30790)Refutation not found, incomplete strategy% (30790)------------------------------
% 2.19/0.66  % (30790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (30790)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.67  % (30790)Memory used [KB]: 10746
% 2.19/0.67  % (30790)Time elapsed: 0.234 s
% 2.19/0.67  % (30790)------------------------------
% 2.19/0.67  % (30790)------------------------------
% 2.19/0.67  % (30782)Refutation not found, incomplete strategy% (30782)------------------------------
% 2.19/0.67  % (30782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (30782)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (30782)Memory used [KB]: 10874
% 2.19/0.67  % (30782)Time elapsed: 0.241 s
% 2.19/0.67  % (30782)------------------------------
% 2.19/0.67  % (30782)------------------------------
% 2.38/0.70  % (30832)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.72/0.74  % (30833)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.72/0.74  % (30831)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.88/0.80  % (30834)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.37/0.84  % (30835)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.37/0.85  % (30836)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.37/0.86  % (30778)Time limit reached!
% 3.37/0.86  % (30778)------------------------------
% 3.37/0.86  % (30778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.86  % (30778)Termination reason: Time limit
% 3.37/0.86  
% 3.37/0.86  % (30778)Memory used [KB]: 8059
% 3.37/0.86  % (30778)Time elapsed: 0.423 s
% 3.37/0.86  % (30778)------------------------------
% 3.37/0.86  % (30778)------------------------------
% 3.67/0.92  % (30832)Refutation not found, incomplete strategy% (30832)------------------------------
% 3.67/0.92  % (30832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.92  % (30832)Termination reason: Refutation not found, incomplete strategy
% 3.67/0.92  
% 3.67/0.92  % (30832)Memory used [KB]: 6396
% 3.67/0.92  % (30832)Time elapsed: 0.278 s
% 3.67/0.92  % (30832)------------------------------
% 3.67/0.92  % (30832)------------------------------
% 3.67/0.94  % (30774)Time limit reached!
% 3.67/0.94  % (30774)------------------------------
% 3.67/0.94  % (30774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.95  % (30774)Termination reason: Time limit
% 4.25/0.95  
% 4.25/0.95  % (30774)Memory used [KB]: 6780
% 4.25/0.95  % (30774)Time elapsed: 0.513 s
% 4.25/0.95  % (30774)------------------------------
% 4.25/0.95  % (30774)------------------------------
% 4.25/0.96  % (30785)Time limit reached!
% 4.25/0.96  % (30785)------------------------------
% 4.25/0.96  % (30785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.96  % (30785)Termination reason: Time limit
% 4.25/0.96  % (30785)Termination phase: Saturation
% 4.25/0.96  
% 4.25/0.96  % (30785)Memory used [KB]: 7931
% 4.25/0.96  % (30785)Time elapsed: 0.500 s
% 4.25/0.96  % (30785)------------------------------
% 4.25/0.96  % (30785)------------------------------
% 4.47/0.98  % (30781)Refutation found. Thanks to Tanya!
% 4.47/0.98  % SZS status Theorem for theBenchmark
% 4.47/0.98  % SZS output start Proof for theBenchmark
% 4.47/0.98  fof(f6309,plain,(
% 4.47/0.98    $false),
% 4.47/0.98    inference(avatar_sat_refutation,[],[f151,f152,f190,f199,f202,f254,f311,f322,f353,f476,f837,f839,f891,f947,f1139,f1187,f1190,f1204,f1206,f1210,f1361,f1915,f2196,f2200,f2253,f2583,f2588,f2821,f3027,f3632,f3674,f3942,f4081,f4459,f4933,f5197,f5491,f6308])).
% 4.47/0.98  fof(f6308,plain,(
% 4.47/0.98    spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101),
% 4.47/0.98    inference(avatar_contradiction_clause,[],[f6307])).
% 4.47/0.98  fof(f6307,plain,(
% 4.47/0.98    $false | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.98    inference(subsumption_resolution,[],[f6306,f2199])).
% 4.47/0.98  fof(f2199,plain,(
% 4.47/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | ~spl6_62),
% 4.47/0.98    inference(avatar_component_clause,[],[f2198])).
% 4.47/0.98  fof(f2198,plain,(
% 4.47/0.98    spl6_62 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)),
% 4.47/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 4.47/0.98  fof(f6306,plain,(
% 4.47/0.98    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.98    inference(forward_demodulation,[],[f6305,f4847])).
% 4.47/0.98  fof(f4847,plain,(
% 4.47/0.98    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_64)),
% 4.47/0.98    inference(subsumption_resolution,[],[f4846,f1572])).
% 4.47/0.98  fof(f1572,plain,(
% 4.47/0.98    v1_relat_1(k1_xboole_0) | ~spl6_8),
% 4.47/0.98    inference(resolution,[],[f1386,f124])).
% 4.47/0.98  fof(f124,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 4.47/0.98    inference(cnf_transformation,[],[f51])).
% 4.47/0.98  fof(f51,plain,(
% 4.47/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.47/0.98    inference(ennf_transformation,[],[f13])).
% 4.47/0.98  fof(f13,axiom,(
% 4.47/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 4.47/0.98  fof(f1386,plain,(
% 4.47/0.98    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~spl6_8),
% 4.47/0.98    inference(backward_demodulation,[],[f329,f1371])).
% 4.47/0.98  fof(f1371,plain,(
% 4.47/0.98    k1_xboole_0 = sK2 | ~spl6_8),
% 4.47/0.98    inference(resolution,[],[f198,f95])).
% 4.47/0.98  fof(f95,plain,(
% 4.47/0.98    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 4.47/0.98    inference(cnf_transformation,[],[f32])).
% 4.47/0.98  fof(f32,plain,(
% 4.47/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.47/0.98    inference(ennf_transformation,[],[f4])).
% 4.47/0.98  fof(f4,axiom,(
% 4.47/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 4.47/0.98  fof(f198,plain,(
% 4.47/0.98    v1_xboole_0(sK2) | ~spl6_8),
% 4.47/0.98    inference(avatar_component_clause,[],[f196])).
% 4.47/0.98  fof(f196,plain,(
% 4.47/0.98    spl6_8 <=> v1_xboole_0(sK2)),
% 4.47/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 4.47/0.98  fof(f329,plain,(
% 4.47/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 4.47/0.98    inference(subsumption_resolution,[],[f328,f175])).
% 4.47/0.98  fof(f175,plain,(
% 4.47/0.98    v1_relat_1(sK2)),
% 4.47/0.98    inference(resolution,[],[f83,f124])).
% 4.47/0.98  fof(f83,plain,(
% 4.47/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 4.47/0.98    inference(cnf_transformation,[],[f61])).
% 4.47/0.98  fof(f61,plain,(
% 4.47/0.98    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f60,f59,f58,f57])).
% 4.47/0.98  fof(f57,plain,(
% 4.47/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.47/0.98    introduced(choice_axiom,[])).
% 4.47/0.98  fof(f58,plain,(
% 4.47/0.98    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 4.47/0.98    introduced(choice_axiom,[])).
% 4.47/0.98  fof(f59,plain,(
% 4.47/0.98    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 4.47/0.98    introduced(choice_axiom,[])).
% 4.47/0.98  fof(f60,plain,(
% 4.47/0.98    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 4.47/0.98    introduced(choice_axiom,[])).
% 4.47/0.98  fof(f56,plain,(
% 4.47/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.47/0.98    inference(flattening,[],[f55])).
% 4.47/0.98  fof(f55,plain,(
% 4.47/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.47/0.98    inference(nnf_transformation,[],[f30])).
% 4.47/0.99  fof(f30,plain,(
% 4.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.47/0.99    inference(flattening,[],[f29])).
% 4.47/0.99  fof(f29,plain,(
% 4.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.47/0.99    inference(ennf_transformation,[],[f26])).
% 4.47/0.99  fof(f26,negated_conjecture,(
% 4.47/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.47/0.99    inference(negated_conjecture,[],[f25])).
% 4.47/0.99  fof(f25,conjecture,(
% 4.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 4.47/0.99  fof(f328,plain,(
% 4.47/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_relat_1(sK2)),
% 4.47/0.99    inference(subsumption_resolution,[],[f241,f155])).
% 4.47/0.99  fof(f155,plain,(
% 4.47/0.99    v1_funct_1(sK2)),
% 4.47/0.99    inference(forward_demodulation,[],[f84,f87])).
% 4.47/0.99  fof(f87,plain,(
% 4.47/0.99    sK2 = sK3),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f84,plain,(
% 4.47/0.99    v1_funct_1(sK3)),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f241,plain,(
% 4.47/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 4.47/0.99    inference(resolution,[],[f211,f112])).
% 4.47/0.99  fof(f112,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f46])).
% 4.47/0.99  fof(f46,plain,(
% 4.47/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.47/0.99    inference(flattening,[],[f45])).
% 4.47/0.99  fof(f45,plain,(
% 4.47/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.47/0.99    inference(ennf_transformation,[],[f19])).
% 4.47/0.99  fof(f19,axiom,(
% 4.47/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 4.47/0.99  fof(f211,plain,(
% 4.47/0.99    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK1))),
% 4.47/0.99    inference(subsumption_resolution,[],[f210,f175])).
% 4.47/0.99  fof(f210,plain,(
% 4.47/0.99    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK1)) | ~v1_relat_1(sK2)),
% 4.47/0.99    inference(resolution,[],[f174,f106])).
% 4.47/0.99  fof(f106,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f68])).
% 4.47/0.99  fof(f68,plain,(
% 4.47/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.47/0.99    inference(nnf_transformation,[],[f42])).
% 4.47/0.99  fof(f42,plain,(
% 4.47/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.47/0.99    inference(ennf_transformation,[],[f11])).
% 4.47/0.99  fof(f11,axiom,(
% 4.47/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 4.47/0.99  fof(f174,plain,(
% 4.47/0.99    v5_relat_1(sK2,u1_struct_0(sK1))),
% 4.47/0.99    inference(resolution,[],[f83,f126])).
% 4.47/0.99  fof(f126,plain,(
% 4.47/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f52])).
% 4.47/0.99  fof(f52,plain,(
% 4.47/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.47/0.99    inference(ennf_transformation,[],[f14])).
% 4.47/0.99  fof(f14,axiom,(
% 4.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 4.47/0.99  fof(f4846,plain,(
% 4.47/0.99    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4845,f2231])).
% 4.47/0.99  fof(f2231,plain,(
% 4.47/0.99    v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl6_8),
% 4.47/0.99    inference(forward_demodulation,[],[f173,f1371])).
% 4.47/0.99  fof(f173,plain,(
% 4.47/0.99    v4_relat_1(sK2,u1_struct_0(sK0))),
% 4.47/0.99    inference(resolution,[],[f83,f125])).
% 4.47/0.99  fof(f125,plain,(
% 4.47/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f52])).
% 4.47/0.99  fof(f4845,plain,(
% 4.47/0.99    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) | ~v1_relat_1(k1_xboole_0) | ~spl6_64),
% 4.47/0.99    inference(resolution,[],[f2246,f113])).
% 4.47/0.99  fof(f113,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f69])).
% 4.47/0.99  fof(f69,plain,(
% 4.47/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.47/0.99    inference(nnf_transformation,[],[f48])).
% 4.47/0.99  fof(f48,plain,(
% 4.47/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.47/0.99    inference(flattening,[],[f47])).
% 4.47/0.99  fof(f47,plain,(
% 4.47/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.47/0.99    inference(ennf_transformation,[],[f17])).
% 4.47/0.99  fof(f17,axiom,(
% 4.47/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 4.47/0.99  fof(f2246,plain,(
% 4.47/0.99    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | ~spl6_64),
% 4.47/0.99    inference(avatar_component_clause,[],[f2244])).
% 4.47/0.99  fof(f2244,plain,(
% 4.47/0.99    spl6_64 <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 4.47/0.99  fof(f6305,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6304,f2195])).
% 4.47/0.99  fof(f2195,plain,(
% 4.47/0.99    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))) ) | ~spl6_61),
% 4.47/0.99    inference(avatar_component_clause,[],[f2194])).
% 4.47/0.99  fof(f2194,plain,(
% 4.47/0.99    spl6_61 <=> ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 4.47/0.99  fof(f6304,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(forward_demodulation,[],[f6303,f4847])).
% 4.47/0.99  fof(f6303,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6302,f2199])).
% 4.47/0.99  fof(f6302,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(forward_demodulation,[],[f6301,f4847])).
% 4.47/0.99  fof(f6301,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6300,f2195])).
% 4.47/0.99  fof(f6300,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(forward_demodulation,[],[f6299,f4847])).
% 4.47/0.99  fof(f6299,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6298,f77])).
% 4.47/0.99  fof(f77,plain,(
% 4.47/0.99    v2_pre_topc(sK0)),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f6298,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6297,f78])).
% 4.47/0.99  fof(f78,plain,(
% 4.47/0.99    l1_pre_topc(sK0)),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f6297,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6296,f1374])).
% 4.47/0.99  fof(f1374,plain,(
% 4.47/0.99    v1_funct_1(k1_xboole_0) | ~spl6_8),
% 4.47/0.99    inference(backward_demodulation,[],[f155,f1371])).
% 4.47/0.99  fof(f6296,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6295,f5538])).
% 4.47/0.99  fof(f5538,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f146,f1371])).
% 4.47/0.99  fof(f146,plain,(
% 4.47/0.99    ~v5_pre_topc(sK2,sK0,sK1) | spl6_1),
% 4.47/0.99    inference(avatar_component_clause,[],[f144])).
% 4.47/0.99  fof(f144,plain,(
% 4.47/0.99    spl6_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 4.47/0.99  fof(f6295,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(resolution,[],[f6286,f5005])).
% 4.47/0.99  fof(f5005,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | v5_pre_topc(X0,X1,sK1) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl6_16),
% 4.47/0.99    inference(subsumption_resolution,[],[f5004,f79])).
% 4.47/0.99  fof(f79,plain,(
% 4.47/0.99    v2_pre_topc(sK1)),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f5004,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X0,X1,sK1) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl6_16),
% 4.47/0.99    inference(subsumption_resolution,[],[f4991,f80])).
% 4.47/0.99  fof(f80,plain,(
% 4.47/0.99    l1_pre_topc(sK1)),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f4991,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X0,X1,sK1) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl6_16),
% 4.47/0.99    inference(superposition,[],[f137,f321])).
% 4.47/0.99  fof(f321,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_16),
% 4.47/0.99    inference(avatar_component_clause,[],[f319])).
% 4.47/0.99  fof(f319,plain,(
% 4.47/0.99    spl6_16 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 4.47/0.99  fof(f137,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f129])).
% 4.47/0.99  fof(f129,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(equality_resolution,[],[f99])).
% 4.47/0.99  fof(f99,plain,(
% 4.47/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f62])).
% 4.47/0.99  fof(f62,plain,(
% 4.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.47/0.99    inference(nnf_transformation,[],[f37])).
% 4.47/0.99  fof(f37,plain,(
% 4.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.47/0.99    inference(flattening,[],[f36])).
% 4.47/0.99  fof(f36,plain,(
% 4.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.47/0.99    inference(ennf_transformation,[],[f24])).
% 4.47/0.99  fof(f24,axiom,(
% 4.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 4.47/0.99  fof(f6286,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6285,f2199])).
% 4.47/0.99  fof(f6285,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6284,f1374])).
% 4.47/0.99  fof(f6284,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_49 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6278,f4823])).
% 4.47/0.99  fof(f4823,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_49)),
% 4.47/0.99    inference(forward_demodulation,[],[f4502,f321])).
% 4.47/0.99  fof(f4502,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_8 | ~spl6_49)),
% 4.47/0.99    inference(forward_demodulation,[],[f1149,f1371])).
% 4.47/0.99  fof(f1149,plain,(
% 4.47/0.99    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_49),
% 4.47/0.99    inference(avatar_component_clause,[],[f1148])).
% 4.47/0.99  fof(f1148,plain,(
% 4.47/0.99    spl6_49 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 4.47/0.99  fof(f6278,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6277,f4905])).
% 4.47/0.99  fof(f4905,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl6_8 | ~spl6_16 | ~spl6_64)),
% 4.47/0.99    inference(backward_demodulation,[],[f4796,f4847])).
% 4.47/0.99  fof(f4796,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl6_8 | ~spl6_16)),
% 4.47/0.99    inference(forward_demodulation,[],[f4505,f321])).
% 4.47/0.99  fof(f4505,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_8),
% 4.47/0.99    inference(forward_demodulation,[],[f153,f1371])).
% 4.47/0.99  fof(f153,plain,(
% 4.47/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.47/0.99    inference(forward_demodulation,[],[f86,f87])).
% 4.47/0.99  fof(f86,plain,(
% 4.47/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  % (30837)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.47/0.99  fof(f6277,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f6274,f5214])).
% 4.47/0.99  fof(f5214,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(backward_demodulation,[],[f4936,f5208])).
% 4.47/0.99  fof(f5208,plain,(
% 4.47/0.99    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5203,f91])).
% 4.47/0.99  fof(f91,plain,(
% 4.47/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f6])).
% 4.47/0.99  fof(f6,axiom,(
% 4.47/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.47/0.99  fof(f5203,plain,(
% 4.47/0.99    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl6_8 | ~spl6_16 | ~spl6_31)),
% 4.47/0.99    inference(resolution,[],[f5200,f117])).
% 4.47/0.99  fof(f117,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f71])).
% 4.47/0.99  fof(f71,plain,(
% 4.47/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.47/0.99    inference(flattening,[],[f70])).
% 4.47/0.99  fof(f70,plain,(
% 4.47/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.47/0.99    inference(nnf_transformation,[],[f5])).
% 4.47/0.99  fof(f5,axiom,(
% 4.47/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.47/0.99  fof(f5200,plain,(
% 4.47/0.99    r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31)),
% 4.47/0.99    inference(forward_demodulation,[],[f5199,f321])).
% 4.47/0.99  fof(f5199,plain,(
% 4.47/0.99    r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),k1_xboole_0) | (~spl6_8 | ~spl6_31)),
% 4.47/0.99    inference(forward_demodulation,[],[f926,f1371])).
% 4.47/0.99  fof(f926,plain,(
% 4.47/0.99    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2) | ~spl6_31),
% 4.47/0.99    inference(avatar_component_clause,[],[f925])).
% 4.47/0.99  fof(f925,plain,(
% 4.47/0.99    spl6_31 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2)),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 4.47/0.99  fof(f4936,plain,(
% 4.47/0.99    m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl6_8 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(forward_demodulation,[],[f3389,f4847])).
% 4.47/0.99  fof(f3389,plain,(
% 4.47/0.99    m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~spl6_101),
% 4.47/0.99    inference(avatar_component_clause,[],[f3388])).
% 4.47/0.99  fof(f3388,plain,(
% 4.47/0.99    spl6_101 <=> m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 4.47/0.99  fof(f6274,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_48 | ~spl6_64)),
% 4.47/0.99    inference(resolution,[],[f5535,f5216])).
% 4.47/0.99  fof(f5216,plain,(
% 4.47/0.99    ( ! [X0] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(backward_demodulation,[],[f5144,f5208])).
% 4.47/0.99  fof(f5144,plain,(
% 4.47/0.99    ( ! [X0] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5143,f77])).
% 4.47/0.99  fof(f5143,plain,(
% 4.47/0.99    ( ! [X0] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v2_pre_topc(sK0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5141,f78])).
% 4.47/0.99  fof(f5141,plain,(
% 4.47/0.99    ( ! [X0] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(superposition,[],[f5025,f4847])).
% 4.47/0.99  fof(f5025,plain,(
% 4.47/0.99    ( ! [X19,X18] : (~v5_pre_topc(X18,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0))) | v5_pre_topc(X18,X19,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X18,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0) | ~v1_funct_1(X18) | ~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),k1_xboole_0))) | ~v1_funct_2(X18,u1_struct_0(X19),k1_xboole_0) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19)) ) | (~spl6_16 | ~spl6_46)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5024,f1098])).
% 4.47/0.99  fof(f1098,plain,(
% 4.47/0.99    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_46),
% 4.47/0.99    inference(avatar_component_clause,[],[f1097])).
% 4.47/0.99  fof(f1097,plain,(
% 4.47/0.99    spl6_46 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 4.47/0.99  fof(f5024,plain,(
% 4.47/0.99    ( ! [X19,X18] : (~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0))) | ~v5_pre_topc(X18,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X18,X19,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X18,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0) | ~v1_funct_1(X18) | ~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),k1_xboole_0))) | ~v1_funct_2(X18,u1_struct_0(X19),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19)) ) | ~spl6_16),
% 4.47/0.99    inference(subsumption_resolution,[],[f5001,f637])).
% 4.47/0.99  fof(f637,plain,(
% 4.47/0.99    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.47/0.99    inference(resolution,[],[f158,f109])).
% 4.47/0.99  fof(f109,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 4.47/0.99    inference(cnf_transformation,[],[f44])).
% 4.47/0.99  fof(f44,plain,(
% 4.47/0.99    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.47/0.99    inference(ennf_transformation,[],[f28])).
% 4.47/0.99  fof(f28,plain,(
% 4.47/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 4.47/0.99    inference(pure_predicate_removal,[],[f20])).
% 4.47/0.99  fof(f20,axiom,(
% 4.47/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 4.47/0.99  fof(f158,plain,(
% 4.47/0.99    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 4.47/0.99    inference(resolution,[],[f80,f94])).
% 4.47/0.99  fof(f94,plain,(
% 4.47/0.99    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.47/0.99    inference(cnf_transformation,[],[f31])).
% 4.47/0.99  fof(f31,plain,(
% 4.47/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.47/0.99    inference(ennf_transformation,[],[f21])).
% 4.47/0.99  fof(f21,axiom,(
% 4.47/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 4.47/0.99  fof(f5001,plain,(
% 4.47/0.99    ( ! [X19,X18] : (~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0))) | ~v5_pre_topc(X18,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X18,X19,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X18,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))),k1_xboole_0) | ~v1_funct_1(X18) | ~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),k1_xboole_0))) | ~v1_funct_2(X18,u1_struct_0(X19),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19)) ) | ~spl6_16),
% 4.47/0.99    inference(superposition,[],[f139,f321])).
% 4.47/0.99  fof(f139,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f131])).
% 4.47/0.99  fof(f131,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(equality_resolution,[],[f101])).
% 4.47/0.99  fof(f101,plain,(
% 4.47/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f63])).
% 4.47/0.99  fof(f63,plain,(
% 4.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.47/0.99    inference(nnf_transformation,[],[f39])).
% 4.47/0.99  fof(f39,plain,(
% 4.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.47/0.99    inference(flattening,[],[f38])).
% 4.47/0.99  fof(f38,plain,(
% 4.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.47/0.99    inference(ennf_transformation,[],[f23])).
% 4.47/0.99  fof(f23,axiom,(
% 4.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 4.47/0.99  fof(f5535,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_8 | ~spl6_48)),
% 4.47/0.99    inference(forward_demodulation,[],[f1124,f1371])).
% 4.47/0.99  fof(f1124,plain,(
% 4.47/0.99    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_48),
% 4.47/0.99    inference(avatar_component_clause,[],[f1122])).
% 4.47/0.99  fof(f1122,plain,(
% 4.47/0.99    spl6_48 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 4.47/0.99  fof(f5491,plain,(
% 4.47/0.99    ~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f5490])).
% 4.47/0.99  fof(f5490,plain,(
% 4.47/0.99    $false | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5489,f2199])).
% 4.47/0.99  fof(f5489,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5488,f1374])).
% 4.47/0.99  fof(f5488,plain,(
% 4.47/0.99    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_49 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5487,f4823])).
% 4.47/0.99  fof(f5487,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5486,f4904])).
% 4.47/0.99  fof(f4904,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_8 | ~spl6_64)),
% 4.47/0.99    inference(backward_demodulation,[],[f4500,f4847])).
% 4.47/0.99  fof(f4500,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f150,f1372])).
% 4.47/0.99  fof(f1372,plain,(
% 4.47/0.99    k1_xboole_0 = sK3 | ~spl6_8),
% 4.47/0.99    inference(backward_demodulation,[],[f87,f1371])).
% 4.47/0.99  fof(f150,plain,(
% 4.47/0.99    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_2),
% 4.47/0.99    inference(avatar_component_clause,[],[f148])).
% 4.47/0.99  fof(f148,plain,(
% 4.47/0.99    spl6_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 4.47/0.99  fof(f5486,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5485,f5388])).
% 4.47/0.99  fof(f5388,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5387,f2199])).
% 4.47/0.99  fof(f5387,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5386,f1374])).
% 4.47/0.99  fof(f5386,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_61 | ~spl6_62 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5349,f2199])).
% 4.47/0.99  fof(f5349,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_61 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5348,f3828])).
% 4.47/0.99  fof(f3828,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_1 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f145,f1371])).
% 4.47/0.99  fof(f145,plain,(
% 4.47/0.99    v5_pre_topc(sK2,sK0,sK1) | ~spl6_1),
% 4.47/0.99    inference(avatar_component_clause,[],[f144])).
% 4.47/0.99  fof(f5348,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_61 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5346,f5214])).
% 4.47/0.99  fof(f5346,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_61 | ~spl6_64)),
% 4.47/0.99    inference(resolution,[],[f5215,f2195])).
% 4.47/0.99  fof(f5215,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,sK0,sK1) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))) ) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_64)),
% 4.47/0.99    inference(backward_demodulation,[],[f5090,f5208])).
% 4.47/0.99  fof(f5090,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))) ) | (~spl6_8 | ~spl6_16 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5089,f77])).
% 4.47/0.99  fof(f5089,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5081,f78])).
% 4.47/0.99  fof(f5081,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_64)),
% 4.47/0.99    inference(superposition,[],[f5007,f4847])).
% 4.47/0.99  fof(f5007,plain,(
% 4.47/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl6_16),
% 4.47/0.99    inference(subsumption_resolution,[],[f5006,f79])).
% 4.47/0.99  fof(f5006,plain,(
% 4.47/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl6_16),
% 4.47/0.99    inference(subsumption_resolution,[],[f4992,f80])).
% 4.47/0.99  fof(f4992,plain,(
% 4.47/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl6_16),
% 4.47/0.99    inference(superposition,[],[f138,f321])).
% 4.47/0.99  fof(f138,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f130])).
% 4.47/0.99  fof(f130,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(equality_resolution,[],[f98])).
% 4.47/0.99  fof(f98,plain,(
% 4.47/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f62])).
% 4.47/0.99  fof(f5485,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5483,f5214])).
% 4.47/0.99  fof(f5483,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(resolution,[],[f5217,f4905])).
% 4.47/0.99  fof(f5217,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_31 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(backward_demodulation,[],[f5160,f5208])).
% 4.47/0.99  fof(f5160,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5159,f77])).
% 4.47/0.99  fof(f5159,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v2_pre_topc(sK0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5150,f78])).
% 4.47/0.99  fof(f5150,plain,(
% 4.47/0.99    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_46 | ~spl6_64)),
% 4.47/0.99    inference(superposition,[],[f5029,f4847])).
% 4.47/0.99  fof(f5029,plain,(
% 4.47/0.99    ( ! [X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0))) | ~v5_pre_topc(X22,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X22,u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0) | ~v1_funct_1(X22) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),k1_xboole_0))) | ~v1_funct_2(X22,u1_struct_0(X23),k1_xboole_0) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23)) ) | (~spl6_16 | ~spl6_46)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5028,f1098])).
% 4.47/0.99  fof(f5028,plain,(
% 4.47/0.99    ( ! [X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0))) | ~v5_pre_topc(X22,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X22,u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0) | ~v1_funct_1(X22) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),k1_xboole_0))) | ~v1_funct_2(X22,u1_struct_0(X23),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23)) ) | ~spl6_16),
% 4.47/0.99    inference(subsumption_resolution,[],[f5003,f637])).
% 4.47/0.99  fof(f5003,plain,(
% 4.47/0.99    ( ! [X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0))) | ~v5_pre_topc(X22,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X22,u1_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))),k1_xboole_0) | ~v1_funct_1(X22) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),k1_xboole_0))) | ~v1_funct_2(X22,u1_struct_0(X23),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X23) | ~v2_pre_topc(X23)) ) | ~spl6_16),
% 4.47/0.99    inference(superposition,[],[f140,f321])).
% 4.47/0.99  fof(f140,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f132])).
% 4.47/0.99  fof(f132,plain,(
% 4.47/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(equality_resolution,[],[f100])).
% 4.47/0.99  fof(f100,plain,(
% 4.47/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f63])).
% 4.47/0.99  fof(f5197,plain,(
% 4.47/0.99    ~spl6_8 | ~spl6_16 | spl6_31 | ~spl6_64 | ~spl6_101),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f5196])).
% 4.47/0.99  fof(f5196,plain,(
% 4.47/0.99    $false | (~spl6_8 | ~spl6_16 | spl6_31 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5195,f90])).
% 4.47/0.99  fof(f90,plain,(
% 4.47/0.99    v1_xboole_0(k1_xboole_0)),
% 4.47/0.99    inference(cnf_transformation,[],[f3])).
% 4.47/0.99  fof(f3,axiom,(
% 4.47/0.99    v1_xboole_0(k1_xboole_0)),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 4.47/0.99  fof(f5195,plain,(
% 4.47/0.99    ~v1_xboole_0(k1_xboole_0) | (~spl6_8 | ~spl6_16 | spl6_31 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f5191,f4801])).
% 4.47/0.99  fof(f4801,plain,(
% 4.47/0.99    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl6_8 | ~spl6_16 | spl6_31)),
% 4.47/0.99    inference(forward_demodulation,[],[f1444,f321])).
% 4.47/0.99  fof(f1444,plain,(
% 4.47/0.99    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl6_8 | spl6_31)),
% 4.47/0.99    inference(backward_demodulation,[],[f1042,f1371])).
% 4.47/0.99  fof(f1042,plain,(
% 4.47/0.99    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl6_31),
% 4.47/0.99    inference(resolution,[],[f994,f102])).
% 4.47/0.99  fof(f102,plain,(
% 4.47/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f67])).
% 4.47/0.99  fof(f67,plain,(
% 4.47/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f65,f66])).
% 4.47/0.99  fof(f66,plain,(
% 4.47/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 4.47/0.99    introduced(choice_axiom,[])).
% 4.47/0.99  fof(f65,plain,(
% 4.47/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.47/0.99    inference(rectify,[],[f64])).
% 4.47/0.99  fof(f64,plain,(
% 4.47/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.47/0.99    inference(nnf_transformation,[],[f1])).
% 4.47/0.99  fof(f1,axiom,(
% 4.47/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 4.47/0.99  fof(f994,plain,(
% 4.47/0.99    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl6_31),
% 4.47/0.99    inference(resolution,[],[f927,f119])).
% 4.47/0.99  fof(f119,plain,(
% 4.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f75])).
% 4.47/0.99  fof(f75,plain,(
% 4.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f73,f74])).
% 4.47/0.99  fof(f74,plain,(
% 4.47/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 4.47/0.99    introduced(choice_axiom,[])).
% 4.47/0.99  fof(f73,plain,(
% 4.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.47/0.99    inference(rectify,[],[f72])).
% 4.47/0.99  fof(f72,plain,(
% 4.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.47/0.99    inference(nnf_transformation,[],[f49])).
% 4.47/0.99  fof(f49,plain,(
% 4.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.47/0.99    inference(ennf_transformation,[],[f2])).
% 4.47/0.99  fof(f2,axiom,(
% 4.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 4.47/0.99  fof(f927,plain,(
% 4.47/0.99    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2) | spl6_31),
% 4.47/0.99    inference(avatar_component_clause,[],[f925])).
% 4.47/0.99  fof(f5191,plain,(
% 4.47/0.99    v1_xboole_0(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | (~spl6_8 | ~spl6_64 | ~spl6_101)),
% 4.47/0.99    inference(resolution,[],[f4936,f108])).
% 4.47/0.99  fof(f108,plain,(
% 4.47/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f43])).
% 4.47/0.99  fof(f43,plain,(
% 4.47/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 4.47/0.99    inference(ennf_transformation,[],[f15])).
% 4.47/0.99  fof(f15,axiom,(
% 4.47/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 4.47/0.99  fof(f4933,plain,(
% 4.47/0.99    ~spl6_8 | ~spl6_64 | spl6_101),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f4932])).
% 4.47/0.99  fof(f4932,plain,(
% 4.47/0.99    $false | (~spl6_8 | ~spl6_64 | spl6_101)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4894,f135])).
% 4.47/0.99  fof(f135,plain,(
% 4.47/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.47/0.99    inference(equality_resolution,[],[f115])).
% 4.47/0.99  fof(f115,plain,(
% 4.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.47/0.99    inference(cnf_transformation,[],[f71])).
% 4.47/0.99  fof(f4894,plain,(
% 4.47/0.99    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl6_8 | ~spl6_64 | spl6_101)),
% 4.47/0.99    inference(backward_demodulation,[],[f3470,f4847])).
% 4.47/0.99  fof(f3470,plain,(
% 4.47/0.99    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) | spl6_101),
% 4.47/0.99    inference(resolution,[],[f3390,f122])).
% 4.47/0.99  fof(f122,plain,(
% 4.47/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f76])).
% 4.47/0.99  fof(f76,plain,(
% 4.47/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.47/0.99    inference(nnf_transformation,[],[f10])).
% 4.47/0.99  fof(f10,axiom,(
% 4.47/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.47/0.99  fof(f3390,plain,(
% 4.47/0.99    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | spl6_101),
% 4.47/0.99    inference(avatar_component_clause,[],[f3388])).
% 4.47/0.99  fof(f4459,plain,(
% 4.47/0.99    ~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f4458])).
% 4.47/0.99  fof(f4458,plain,(
% 4.47/0.99    $false | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4457,f2385])).
% 4.47/0.99  fof(f2385,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f1387,f189])).
% 4.47/0.99  fof(f189,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(sK1) | ~spl6_6),
% 4.47/0.99    inference(avatar_component_clause,[],[f187])).
% 4.47/0.99  fof(f187,plain,(
% 4.47/0.99    spl6_6 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 4.47/0.99  fof(f1387,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~spl6_8),
% 4.47/0.99    inference(backward_demodulation,[],[f331,f1371])).
% 4.47/0.99  fof(f331,plain,(
% 4.47/0.99    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 4.47/0.99    inference(subsumption_resolution,[],[f330,f175])).
% 4.47/0.99  fof(f330,plain,(
% 4.47/0.99    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_relat_1(sK2)),
% 4.47/0.99    inference(subsumption_resolution,[],[f240,f155])).
% 4.47/0.99  fof(f240,plain,(
% 4.47/0.99    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 4.47/0.99    inference(resolution,[],[f211,f111])).
% 4.47/0.99  fof(f111,plain,(
% 4.47/0.99    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f46])).
% 4.47/0.99  fof(f4457,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4456,f2386])).
% 4.47/0.99  fof(f2386,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f1386,f189])).
% 4.47/0.99  fof(f4456,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4455,f1374])).
% 4.47/0.99  fof(f4455,plain,(
% 4.47/0.99    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4454,f2652])).
% 4.47/0.99  fof(f2652,plain,(
% 4.47/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2651,f1572])).
% 4.47/0.99  fof(f2651,plain,(
% 4.47/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2650,f1374])).
% 4.47/0.99  fof(f2650,plain,(
% 4.47/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2647,f91])).
% 4.47/0.99  fof(f2647,plain,(
% 4.47/0.99    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(superposition,[],[f111,f2416])).
% 4.47/0.99  fof(f2416,plain,(
% 4.47/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(forward_demodulation,[],[f2271,f189])).
% 4.47/0.99  fof(f2271,plain,(
% 4.47/0.99    u1_struct_0(sK1) = k2_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(forward_demodulation,[],[f253,f1371])).
% 4.47/0.99  fof(f253,plain,(
% 4.47/0.99    u1_struct_0(sK1) = k2_relat_1(sK2) | ~spl6_11),
% 4.47/0.99    inference(avatar_component_clause,[],[f251])).
% 4.47/0.99  fof(f251,plain,(
% 4.47/0.99    spl6_11 <=> u1_struct_0(sK1) = k2_relat_1(sK2)),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 4.47/0.99  fof(f4454,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4453,f3827])).
% 4.47/0.99  fof(f3827,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_2 | ~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f3826,f1372])).
% 4.47/0.99  fof(f3826,plain,(
% 4.47/0.99    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_2 | ~spl6_6)),
% 4.47/0.99    inference(forward_demodulation,[],[f150,f189])).
% 4.47/0.99  fof(f4453,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4451,f4337])).
% 4.47/0.99  fof(f4337,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4336,f2374])).
% 4.47/0.99  fof(f2374,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f2237,f189])).
% 4.47/0.99  fof(f2237,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_8),
% 4.47/0.99    inference(forward_demodulation,[],[f82,f1371])).
% 4.47/0.99  fof(f82,plain,(
% 4.47/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f4336,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4335,f2386])).
% 4.47/0.99  fof(f4335,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4334,f1374])).
% 4.47/0.99  fof(f4334,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4333,f2385])).
% 4.47/0.99  fof(f4333,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4331,f3828])).
% 4.47/0.99  fof(f4331,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(resolution,[],[f4191,f2375])).
% 4.47/0.99  fof(f2375,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f2236,f189])).
% 4.47/0.99  fof(f2236,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_8),
% 4.47/0.99    inference(forward_demodulation,[],[f83,f1371])).
% 4.47/0.99  fof(f4191,plain,(
% 4.47/0.99    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v5_pre_topc(X11,sK0,sK1) | v5_pre_topc(X11,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(X11,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X11) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X11,u1_struct_0(sK0),k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4190,f77])).
% 4.47/0.99  fof(f4190,plain,(
% 4.47/0.99    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v5_pre_topc(X11,sK0,sK1) | v5_pre_topc(X11,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(X11,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X11) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(X11,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4154,f78])).
% 4.47/0.99  fof(f4154,plain,(
% 4.47/0.99    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v5_pre_topc(X11,sK0,sK1) | v5_pre_topc(X11,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(X11,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X11) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(X11,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(superposition,[],[f2637,f4133])).
% 4.47/0.99  fof(f4133,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4132,f1572])).
% 4.47/0.99  fof(f4132,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4131,f2665])).
% 4.47/0.99  fof(f2665,plain,(
% 4.47/0.99    v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(resolution,[],[f2597,f125])).
% 4.47/0.99  fof(f2597,plain,(
% 4.47/0.99    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f2596,f1371])).
% 4.47/0.99  fof(f2596,plain,(
% 4.47/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~spl6_6),
% 4.47/0.99    inference(forward_demodulation,[],[f153,f189])).
% 4.47/0.99  fof(f4131,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(k1_xboole_0) | ~spl6_117),
% 4.47/0.99    inference(resolution,[],[f3662,f113])).
% 4.47/0.99  fof(f3662,plain,(
% 4.47/0.99    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_117),
% 4.47/0.99    inference(avatar_component_clause,[],[f3660])).
% 4.47/0.99  fof(f3660,plain,(
% 4.47/0.99    spl6_117 <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).
% 4.47/0.99  fof(f2637,plain,(
% 4.47/0.99    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0))) | ~v5_pre_topc(X14,X15,sK1) | v5_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)),sK1) | ~v1_funct_2(X14,u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | ~spl6_6),
% 4.47/0.99    inference(subsumption_resolution,[],[f2636,f79])).
% 4.47/0.99  fof(f2636,plain,(
% 4.47/0.99    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0))) | ~v5_pre_topc(X14,X15,sK1) | v5_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)),sK1) | ~v1_funct_2(X14,u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | ~spl6_6),
% 4.47/0.99    inference(subsumption_resolution,[],[f2621,f80])).
% 4.47/0.99  fof(f2621,plain,(
% 4.47/0.99    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0))) | ~v5_pre_topc(X14,X15,sK1) | v5_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)),sK1) | ~v1_funct_2(X14,u1_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))),k1_xboole_0) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | ~spl6_6),
% 4.47/0.99    inference(superposition,[],[f140,f189])).
% 4.47/0.99  fof(f4451,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(resolution,[],[f4245,f2655])).
% 4.47/0.99  fof(f2655,plain,(
% 4.47/0.99    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2654,f1572])).
% 4.47/0.99  fof(f2654,plain,(
% 4.47/0.99    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2653,f1374])).
% 4.47/0.99  fof(f2653,plain,(
% 4.47/0.99    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2648,f91])).
% 4.47/0.99  fof(f2648,plain,(
% 4.47/0.99    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11)),
% 4.47/0.99    inference(superposition,[],[f112,f2416])).
% 4.47/0.99  fof(f4245,plain,(
% 4.47/0.99    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_68 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4244,f2771])).
% 4.47/0.99  fof(f2771,plain,(
% 4.47/0.99    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_68),
% 4.47/0.99    inference(avatar_component_clause,[],[f2770])).
% 4.47/0.99  fof(f2770,plain,(
% 4.47/0.99    spl6_68 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 4.47/0.99  fof(f4244,plain,(
% 4.47/0.99    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4237,f159])).
% 4.47/0.99  fof(f159,plain,(
% 4.47/0.99    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.47/0.99    inference(resolution,[],[f157,f109])).
% 4.47/0.99  fof(f157,plain,(
% 4.47/0.99    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.47/0.99    inference(resolution,[],[f78,f94])).
% 4.47/0.99  fof(f4237,plain,(
% 4.47/0.99    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl6_6 | ~spl6_8 | ~spl6_117)),
% 4.47/0.99    inference(superposition,[],[f2629,f4133])).
% 4.47/0.99  fof(f2629,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl6_6),
% 4.47/0.99    inference(subsumption_resolution,[],[f2628,f79])).
% 4.47/0.99  fof(f2628,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl6_6),
% 4.47/0.99    inference(subsumption_resolution,[],[f2617,f80])).
% 4.47/0.99  fof(f2617,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl6_6),
% 4.47/0.99    inference(superposition,[],[f138,f189])).
% 4.47/0.99  fof(f4081,plain,(
% 4.47/0.99    ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_55 | ~spl6_118),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f4080])).
% 4.47/0.99  fof(f4080,plain,(
% 4.47/0.99    $false | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_55 | ~spl6_118)),
% 4.47/0.99    inference(subsumption_resolution,[],[f4079,f3669])).
% 4.47/0.99  fof(f3669,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_118),
% 4.47/0.99    inference(avatar_component_clause,[],[f3667])).
% 4.47/0.99  fof(f3667,plain,(
% 4.47/0.99    spl6_118 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).
% 4.47/0.99  fof(f4079,plain,(
% 4.47/0.99    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f4078,f189])).
% 4.47/0.99  fof(f4078,plain,(
% 4.47/0.99    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f1679,f2416])).
% 4.47/0.99  fof(f1679,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k2_relat_1(k1_xboole_0) | spl6_55),
% 4.47/0.99    inference(avatar_component_clause,[],[f1678])).
% 4.47/0.99  fof(f1678,plain,(
% 4.47/0.99    spl6_55 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0)),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 4.47/0.99  fof(f3942,plain,(
% 4.47/0.99    ~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f3941])).
% 4.47/0.99  fof(f3941,plain,(
% 4.47/0.99    $false | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3940,f77])).
% 4.47/0.99  fof(f3940,plain,(
% 4.47/0.99    ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3939,f78])).
% 4.47/0.99  fof(f3939,plain,(
% 4.47/0.99    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3938,f1374])).
% 4.47/0.99  fof(f3938,plain,(
% 4.47/0.99    ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3937,f3848])).
% 4.47/0.99  fof(f3848,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3847,f2374])).
% 4.47/0.99  fof(f3847,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f3846,f3685])).
% 4.47/0.99  fof(f3685,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f3684,f189])).
% 4.47/0.99  fof(f3684,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f1680,f2416])).
% 4.47/0.99  fof(f1680,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0) | ~spl6_55),
% 4.47/0.99    inference(avatar_component_clause,[],[f1678])).
% 4.47/0.99  fof(f3846,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3845,f2375])).
% 4.47/0.99  fof(f3845,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f3844,f3685])).
% 4.47/0.99  fof(f3844,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3843,f3705])).
% 4.47/0.99  fof(f3705,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(backward_demodulation,[],[f2599,f3685])).
% 4.47/0.99  fof(f2599,plain,(
% 4.47/0.99    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(forward_demodulation,[],[f2598,f1371])).
% 4.47/0.99  fof(f2598,plain,(
% 4.47/0.99    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_6),
% 4.47/0.99    inference(forward_demodulation,[],[f154,f189])).
% 4.47/0.99  fof(f154,plain,(
% 4.47/0.99    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.47/0.99    inference(forward_demodulation,[],[f85,f87])).
% 4.47/0.99  fof(f85,plain,(
% 4.47/0.99    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.47/0.99    inference(cnf_transformation,[],[f61])).
% 4.47/0.99  fof(f3843,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_46 | ~spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f3842,f3685])).
% 4.47/0.99  fof(f3842,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_46)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3841,f77])).
% 4.47/0.99  fof(f3841,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_46)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3840,f78])).
% 4.47/0.99  fof(f3840,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_46)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3839,f2390])).
% 4.47/0.99  fof(f2390,plain,(
% 4.47/0.99    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_46)),
% 4.47/0.99    inference(forward_demodulation,[],[f1098,f189])).
% 4.47/0.99  fof(f3839,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3838,f454])).
% 4.47/0.99  fof(f454,plain,(
% 4.47/0.99    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_17),
% 4.47/0.99    inference(avatar_component_clause,[],[f453])).
% 4.47/0.99  fof(f453,plain,(
% 4.47/0.99    spl6_17 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.47/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 4.47/0.99  fof(f3838,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_2 | ~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3837,f1374])).
% 4.47/0.99  fof(f3837,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_2 | ~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2662,f3827])).
% 4.47/0.99  fof(f2662,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(resolution,[],[f2597,f140])).
% 4.47/0.99  fof(f3937,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3936,f3828])).
% 4.47/0.99  fof(f3936,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3930,f2374])).
% 4.47/0.99  fof(f3930,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(resolution,[],[f3779,f2375])).
% 4.47/0.99  fof(f3779,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f3778])).
% 4.47/0.99  fof(f3778,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(forward_demodulation,[],[f3773,f3685])).
% 4.47/0.99  fof(f3773,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f3707])).
% 4.47/0.99  fof(f3707,plain,(
% 4.47/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,sK1) | v5_pre_topc(X6,X7,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_55)),
% 4.47/0.99    inference(backward_demodulation,[],[f2629,f3685])).
% 4.47/0.99  fof(f3674,plain,(
% 4.47/0.99    spl6_117 | spl6_118 | ~spl6_6 | ~spl6_8),
% 4.47/0.99    inference(avatar_split_clause,[],[f3673,f196,f187,f3667,f3660])).
% 4.47/0.99  fof(f3673,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3672,f1374])).
% 4.47/0.99  fof(f3672,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(subsumption_resolution,[],[f2664,f2599])).
% 4.47/0.99  fof(f2664,plain,(
% 4.47/0.99    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 4.47/0.99    inference(resolution,[],[f2597,f142])).
% 4.47/0.99  fof(f142,plain,(
% 4.47/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.47/0.99    inference(duplicate_literal_removal,[],[f127])).
% 4.47/0.99  fof(f127,plain,(
% 4.47/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.47/0.99    inference(cnf_transformation,[],[f54])).
% 4.47/0.99  fof(f54,plain,(
% 4.47/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.47/0.99    inference(flattening,[],[f53])).
% 4.47/0.99  fof(f53,plain,(
% 4.47/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.47/0.99    inference(ennf_transformation,[],[f18])).
% 4.47/0.99  fof(f18,axiom,(
% 4.47/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 4.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 4.47/0.99  fof(f3632,plain,(
% 4.47/0.99    spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68),
% 4.47/0.99    inference(avatar_contradiction_clause,[],[f3631])).
% 4.47/0.99  fof(f3631,plain,(
% 4.47/0.99    $false | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3630,f2374])).
% 4.47/0.99  fof(f3630,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(forward_demodulation,[],[f3629,f189])).
% 4.47/0.99  fof(f3629,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3628,f2375])).
% 4.47/0.99  fof(f3628,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(forward_demodulation,[],[f3627,f189])).
% 4.47/0.99  fof(f3627,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3626,f79])).
% 4.47/0.99  fof(f3626,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3625,f80])).
% 4.47/0.99  fof(f3625,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3624,f1374])).
% 4.47/0.99  fof(f3624,plain,(
% 4.47/0.99    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3623,f2652])).
% 4.47/0.99  fof(f3623,plain,(
% 4.47/0.99    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3622,f1373])).
% 4.47/0.99  fof(f1373,plain,(
% 4.47/0.99    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_8)),
% 4.47/0.99    inference(backward_demodulation,[],[f146,f1371])).
% 4.47/0.99  fof(f3622,plain,(
% 4.47/0.99    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3614,f2655])).
% 4.47/0.99  fof(f3614,plain,(
% 4.47/0.99    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/0.99    inference(resolution,[],[f3612,f3154])).
% 4.47/0.99  fof(f3154,plain,(
% 4.47/0.99    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3153,f77])).
% 4.47/0.99  fof(f3153,plain,(
% 4.47/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3)))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X3) | v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~v2_pre_topc(sK0)) ) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3139,f78])).
% 4.47/0.99  fof(f3139,plain,(
% 4.47/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3)))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X3) | v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(superposition,[],[f139,f3132])).
% 4.47/0.99  fof(f3132,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3131,f1572])).
% 4.47/0.99  fof(f3131,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3130,f2665])).
% 4.47/0.99  fof(f3130,plain,(
% 4.47/0.99    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(resolution,[],[f3095,f113])).
% 4.47/0.99  fof(f3095,plain,(
% 4.47/0.99    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/0.99    inference(subsumption_resolution,[],[f3094,f1374])).
% 4.47/1.00  fof(f3094,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3093,f2599])).
% 4.47/1.00  fof(f3093,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2664,f3090])).
% 4.47/1.00  fof(f3090,plain,(
% 4.47/1.00    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | spl6_16)),
% 4.47/1.00    inference(forward_demodulation,[],[f320,f189])).
% 4.47/1.00  fof(f320,plain,(
% 4.47/1.00    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_16),
% 4.47/1.00    inference(avatar_component_clause,[],[f319])).
% 4.47/1.00  fof(f3612,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3611,f2385])).
% 4.47/1.00  fof(f3611,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3610,f2386])).
% 4.47/1.00  fof(f3610,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3609,f1374])).
% 4.47/1.00  fof(f3609,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3608,f2652])).
% 4.47/1.00  fof(f3608,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3607,f2655])).
% 4.47/1.00  fof(f3607,plain,(
% 4.47/1.00    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(resolution,[],[f3186,f2376])).
% 4.47/1.00  fof(f2376,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_6 | ~spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f2218,f189])).
% 4.47/1.00  fof(f2218,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f149,f1372])).
% 4.47/1.00  fof(f149,plain,(
% 4.47/1.00    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_2),
% 4.47/1.00    inference(avatar_component_clause,[],[f148])).
% 4.47/1.00  fof(f3186,plain,(
% 4.47/1.00    ( ! [X2] : (~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_6 | ~spl6_8 | spl6_16 | ~spl6_68)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3185,f2771])).
% 4.47/1.00  fof(f3185,plain,(
% 4.47/1.00    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3176,f159])).
% 4.47/1.00  fof(f3176,plain,(
% 4.47/1.00    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_2(X2,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl6_6 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(superposition,[],[f2625,f3132])).
% 4.47/1.00  fof(f2625,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl6_6),
% 4.47/1.00    inference(subsumption_resolution,[],[f2624,f79])).
% 4.47/1.00  fof(f2624,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl6_6),
% 4.47/1.00    inference(subsumption_resolution,[],[f2615,f80])).
% 4.47/1.00  fof(f2615,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl6_6),
% 4.47/1.00    inference(superposition,[],[f137,f189])).
% 4.47/1.00  fof(f3027,plain,(
% 4.47/1.00    spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f3026])).
% 4.47/1.00  fof(f3026,plain,(
% 4.47/1.00    $false | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3025,f77])).
% 4.47/1.00  fof(f3025,plain,(
% 4.47/1.00    ~v2_pre_topc(sK0) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3024,f78])).
% 4.47/1.00  fof(f3024,plain,(
% 4.47/1.00    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3023,f1374])).
% 4.47/1.00  fof(f3023,plain,(
% 4.47/1.00    ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3022,f1373])).
% 4.47/1.00  fof(f3022,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3021,f2374])).
% 4.47/1.00  fof(f3021,plain,(
% 4.47/1.00    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f3015,f2375])).
% 4.47/1.00  fof(f3015,plain,(
% 4.47/1.00    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(resolution,[],[f2871,f2900])).
% 4.47/1.00  fof(f2900,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2899,f2374])).
% 4.47/1.00  fof(f2899,plain,(
% 4.47/1.00    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(forward_demodulation,[],[f2898,f2831])).
% 4.47/1.00  fof(f2831,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f2830,f189])).
% 4.47/1.00  fof(f2830,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f2829,f2416])).
% 4.47/1.00  fof(f2829,plain,(
% 4.47/1.00    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f946,f1371])).
% 4.47/1.00  fof(f946,plain,(
% 4.47/1.00    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(sK2) | ~spl6_34),
% 4.47/1.00    inference(avatar_component_clause,[],[f944])).
% 4.47/1.00  fof(f944,plain,(
% 4.47/1.00    spl6_34 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(sK2)),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 4.47/1.00  fof(f2898,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2897,f2375])).
% 4.47/1.00  fof(f2897,plain,(
% 4.47/1.00    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(forward_demodulation,[],[f2896,f2831])).
% 4.47/1.00  fof(f2896,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2895,f2858])).
% 4.47/1.00  fof(f2858,plain,(
% 4.47/1.00    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(backward_demodulation,[],[f2599,f2831])).
% 4.47/1.00  fof(f2895,plain,(
% 4.47/1.00    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_17 | ~spl6_34 | ~spl6_46)),
% 4.47/1.00    inference(forward_demodulation,[],[f2894,f2831])).
% 4.47/1.00  fof(f2894,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2893,f77])).
% 4.47/1.00  fof(f2893,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2892,f78])).
% 4.47/1.00  fof(f2892,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_46)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2891,f2390])).
% 4.47/1.00  fof(f2891,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_17)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2890,f454])).
% 4.47/1.00  fof(f2890,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2889,f1374])).
% 4.47/1.00  fof(f2889,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_6 | ~spl6_8)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2663,f2376])).
% 4.47/1.00  fof(f2663,plain,(
% 4.47/1.00    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_6 | ~spl6_8)),
% 4.47/1.00    inference(resolution,[],[f2597,f139])).
% 4.47/1.00  fof(f2871,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f2870])).
% 4.47/1.00  fof(f2870,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f2866,f2831])).
% 4.47/1.00  fof(f2866,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f2859])).
% 4.47/1.00  fof(f2859,plain,(
% 4.47/1.00    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v5_pre_topc(X2,X3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X2,X3,sK1) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_34)),
% 4.47/1.00    inference(backward_demodulation,[],[f2625,f2831])).
% 4.47/1.00  fof(f2821,plain,(
% 4.47/1.00    spl6_68),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f2820])).
% 4.47/1.00  fof(f2820,plain,(
% 4.47/1.00    $false | spl6_68),
% 4.47/1.00    inference(subsumption_resolution,[],[f2819,f77])).
% 4.47/1.00  fof(f2819,plain,(
% 4.47/1.00    ~v2_pre_topc(sK0) | spl6_68),
% 4.47/1.00    inference(subsumption_resolution,[],[f2818,f78])).
% 4.47/1.00  fof(f2818,plain,(
% 4.47/1.00    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl6_68),
% 4.47/1.00    inference(resolution,[],[f2772,f97])).
% 4.47/1.00  fof(f97,plain,(
% 4.47/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.47/1.00    inference(cnf_transformation,[],[f35])).
% 4.47/1.00  fof(f35,plain,(
% 4.47/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.47/1.00    inference(flattening,[],[f34])).
% 4.47/1.00  fof(f34,plain,(
% 4.47/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.47/1.00    inference(ennf_transformation,[],[f27])).
% 4.47/1.00  fof(f27,plain,(
% 4.47/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 4.47/1.00    inference(pure_predicate_removal,[],[f22])).
% 4.47/1.00  fof(f22,axiom,(
% 4.47/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 4.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 4.47/1.00  fof(f2772,plain,(
% 4.47/1.00    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_68),
% 4.47/1.00    inference(avatar_component_clause,[],[f2770])).
% 4.47/1.00  fof(f2588,plain,(
% 4.47/1.00    ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_16 | spl6_34),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f2587])).
% 4.47/1.00  fof(f2587,plain,(
% 4.47/1.00    $false | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_16 | spl6_34)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2586,f2404])).
% 4.47/1.00  fof(f2404,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_16)),
% 4.47/1.00    inference(forward_demodulation,[],[f321,f189])).
% 4.47/1.00  fof(f2586,plain,(
% 4.47/1.00    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f2585,f189])).
% 4.47/1.00  fof(f2585,plain,(
% 4.47/1.00    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f2584,f2416])).
% 4.47/1.00  fof(f2584,plain,(
% 4.47/1.00    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k2_relat_1(k1_xboole_0) | (~spl6_8 | spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f945,f1371])).
% 4.47/1.00  fof(f945,plain,(
% 4.47/1.00    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k2_relat_1(sK2) | spl6_34),
% 4.47/1.00    inference(avatar_component_clause,[],[f944])).
% 4.47/1.00  fof(f2583,plain,(
% 4.47/1.00    ~spl6_8 | spl6_57),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f2582])).
% 4.47/1.00  fof(f2582,plain,(
% 4.47/1.00    $false | (~spl6_8 | spl6_57)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2179,f1572])).
% 4.47/1.00  fof(f2179,plain,(
% 4.47/1.00    ~v1_relat_1(k1_xboole_0) | spl6_57),
% 4.47/1.00    inference(avatar_component_clause,[],[f2177])).
% 4.47/1.00  fof(f2177,plain,(
% 4.47/1.00    spl6_57 <=> v1_relat_1(k1_xboole_0)),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 4.47/1.00  fof(f2253,plain,(
% 4.47/1.00    spl6_6 | spl6_64 | ~spl6_8),
% 4.47/1.00    inference(avatar_split_clause,[],[f2252,f196,f2244,f187])).
% 4.47/1.00  fof(f2252,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | ~spl6_8),
% 4.47/1.00    inference(subsumption_resolution,[],[f2251,f1374])).
% 4.47/1.00  fof(f2251,plain,(
% 4.47/1.00    ~v1_funct_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | ~spl6_8),
% 4.47/1.00    inference(forward_demodulation,[],[f2250,f1371])).
% 4.47/1.00  fof(f2250,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_1(sK2) | ~spl6_8),
% 4.47/1.00    inference(subsumption_resolution,[],[f2249,f2237])).
% 4.47/1.00  fof(f2249,plain,(
% 4.47/1.00    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_1(sK2) | ~spl6_8),
% 4.47/1.00    inference(forward_demodulation,[],[f2248,f1371])).
% 4.47/1.00  fof(f2248,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl6_8),
% 4.47/1.00    inference(forward_demodulation,[],[f707,f1371])).
% 4.47/1.00  fof(f707,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 4.47/1.00    inference(resolution,[],[f83,f142])).
% 4.47/1.00  fof(f2200,plain,(
% 4.47/1.00    ~spl6_57 | spl6_62 | ~spl6_8 | ~spl6_16 | ~spl6_34),
% 4.47/1.00    inference(avatar_split_clause,[],[f2023,f944,f319,f196,f2198,f2177])).
% 4.47/1.00  fof(f2023,plain,(
% 4.47/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2022,f1374])).
% 4.47/1.00  fof(f2022,plain,(
% 4.47/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2019,f91])).
% 4.47/1.00  fof(f2019,plain,(
% 4.47/1.00    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(superposition,[],[f111,f1923])).
% 4.47/1.00  fof(f1923,plain,(
% 4.47/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(backward_demodulation,[],[f1709,f321])).
% 4.47/1.00  fof(f1709,plain,(
% 4.47/1.00    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_34)),
% 4.47/1.00    inference(forward_demodulation,[],[f946,f1371])).
% 4.47/1.00  fof(f2196,plain,(
% 4.47/1.00    ~spl6_57 | spl6_61 | ~spl6_8 | ~spl6_16 | ~spl6_34),
% 4.47/1.00    inference(avatar_split_clause,[],[f2026,f944,f319,f196,f2194,f2177])).
% 4.47/1.00  fof(f2026,plain,(
% 4.47/1.00    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2025,f1374])).
% 4.47/1.00  fof(f2025,plain,(
% 4.47/1.00    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(subsumption_resolution,[],[f2020,f91])).
% 4.47/1.00  fof(f2020,plain,(
% 4.47/1.00    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_16 | ~spl6_34)),
% 4.47/1.00    inference(superposition,[],[f112,f1923])).
% 4.47/1.00  fof(f1915,plain,(
% 4.47/1.00    spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1914])).
% 4.47/1.00  fof(f1914,plain,(
% 4.47/1.00    $false | (spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1913,f79])).
% 4.47/1.00  fof(f1913,plain,(
% 4.47/1.00    ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1912,f80])).
% 4.47/1.00  fof(f1912,plain,(
% 4.47/1.00    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1911,f1374])).
% 4.47/1.00  fof(f1911,plain,(
% 4.47/1.00    ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1910,f1373])).
% 4.47/1.00  fof(f1910,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1909,f1387])).
% 4.47/1.00  fof(f1909,plain,(
% 4.47/1.00    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1899,f1386])).
% 4.47/1.00  fof(f1899,plain,(
% 4.47/1.00    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | ~spl6_8 | ~spl6_14 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(resolution,[],[f1786,f1385])).
% 4.47/1.00  fof(f1385,plain,(
% 4.47/1.00    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),sK1) | (~spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(backward_demodulation,[],[f310,f1371])).
% 4.47/1.00  fof(f310,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~spl6_14),
% 4.47/1.00    inference(avatar_component_clause,[],[f308])).
% 4.47/1.00  fof(f308,plain,(
% 4.47/1.00    spl6_14 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 4.47/1.00  fof(f1786,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9)) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f1785])).
% 4.47/1.00  fof(f1785,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9)) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(forward_demodulation,[],[f1778,f1764])).
% 4.47/1.00  fof(f1764,plain,(
% 4.47/1.00    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))) | (~spl6_5 | ~spl6_8 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1763,f953])).
% 4.47/1.00  fof(f953,plain,(
% 4.47/1.00    v1_relat_1(k1_xboole_0) | (~spl6_5 | ~spl6_19)),
% 4.47/1.00    inference(resolution,[],[f892,f124])).
% 4.47/1.00  fof(f892,plain,(
% 4.47/1.00    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl6_5 | ~spl6_19)),
% 4.47/1.00    inference(forward_demodulation,[],[f462,f717])).
% 4.47/1.00  fof(f717,plain,(
% 4.47/1.00    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f716,f175])).
% 4.47/1.00  fof(f716,plain,(
% 4.47/1.00    u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f715,f173])).
% 4.47/1.00  fof(f715,plain,(
% 4.47/1.00    u1_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f185,f113])).
% 4.47/1.00  fof(f185,plain,(
% 4.47/1.00    v1_partfun1(sK2,u1_struct_0(sK0)) | ~spl6_5),
% 4.47/1.00    inference(avatar_component_clause,[],[f183])).
% 4.47/1.00  fof(f183,plain,(
% 4.47/1.00    spl6_5 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 4.47/1.00  fof(f462,plain,(
% 4.47/1.00    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~spl6_19),
% 4.47/1.00    inference(avatar_component_clause,[],[f461])).
% 4.47/1.00  fof(f461,plain,(
% 4.47/1.00    spl6_19 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 4.47/1.00  fof(f1763,plain,(
% 4.47/1.00    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))) | ~v1_relat_1(k1_xboole_0) | (~spl6_5 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1762,f1401])).
% 4.47/1.00  fof(f1401,plain,(
% 4.47/1.00    v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(backward_demodulation,[],[f747,f1371])).
% 4.47/1.00  fof(f747,plain,(
% 4.47/1.00    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f720,f125])).
% 4.47/1.00  fof(f720,plain,(
% 4.47/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_5),
% 4.47/1.00    inference(backward_demodulation,[],[f153,f717])).
% 4.47/1.00  fof(f1762,plain,(
% 4.47/1.00    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))) | ~v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))) | ~v1_relat_1(k1_xboole_0) | (~spl6_5 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(resolution,[],[f1691,f113])).
% 4.47/1.00  fof(f1691,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))) | (~spl6_5 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1690,f1374])).
% 4.47/1.00  fof(f1690,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_5 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1689,f1390])).
% 4.47/1.00  fof(f1390,plain,(
% 4.47/1.00    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(backward_demodulation,[],[f721,f1371])).
% 4.47/1.00  fof(f721,plain,(
% 4.47/1.00    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(backward_demodulation,[],[f154,f717])).
% 4.47/1.00  fof(f1689,plain,(
% 4.47/1.00    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_5 | ~spl6_8 | spl6_16)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1514,f320])).
% 4.47/1.00  fof(f1514,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(resolution,[],[f1389,f142])).
% 4.47/1.00  fof(f1389,plain,(
% 4.47/1.00    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(backward_demodulation,[],[f720,f1371])).
% 4.47/1.00  fof(f1778,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9)) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f1771])).
% 4.47/1.00  fof(f1771,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8 | spl6_16 | ~spl6_19)),
% 4.47/1.00    inference(backward_demodulation,[],[f1472,f1764])).
% 4.47/1.00  fof(f1472,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v1_funct_2(X8,k1_relat_1(k1_xboole_0),u1_struct_0(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)))) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f1471,f1371])).
% 4.47/1.00  fof(f1471,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X9)))) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)))) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f1470,f1371])).
% 4.47/1.00  fof(f1470,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)))) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f1469,f1371])).
% 4.47/1.00  fof(f1469,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)))) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f1409,f1371])).
% 4.47/1.00  fof(f1409,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | ~spl6_8)),
% 4.47/1.00    inference(backward_demodulation,[],[f776,f1371])).
% 4.47/1.00  fof(f776,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f775,f77])).
% 4.47/1.00  fof(f775,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~v2_pre_topc(sK0)) ) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f761,f78])).
% 4.47/1.00  fof(f761,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl6_5),
% 4.47/1.00    inference(superposition,[],[f139,f717])).
% 4.47/1.00  fof(f1361,plain,(
% 4.47/1.00    spl6_1 | ~spl6_5 | spl6_8 | ~spl6_14),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1360])).
% 4.47/1.00  fof(f1360,plain,(
% 4.47/1.00    $false | (spl6_1 | ~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1359,f79])).
% 4.47/1.00  fof(f1359,plain,(
% 4.47/1.00    ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1358,f80])).
% 4.47/1.00  fof(f1358,plain,(
% 4.47/1.00    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1357,f155])).
% 4.47/1.00  fof(f1357,plain,(
% 4.47/1.00    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl6_1 | ~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1356,f146])).
% 4.47/1.00  fof(f1356,plain,(
% 4.47/1.00    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1355,f331])).
% 4.47/1.00  fof(f1355,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1347,f329])).
% 4.47/1.00  fof(f1347,plain,(
% 4.47/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | spl6_8 | ~spl6_14)),
% 4.47/1.00    inference(resolution,[],[f1248,f310])).
% 4.47/1.00  fof(f1248,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f1247])).
% 4.47/1.00  fof(f1247,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_1(X8) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(forward_demodulation,[],[f1240,f1225])).
% 4.47/1.00  fof(f1225,plain,(
% 4.47/1.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1224,f175])).
% 4.47/1.00  fof(f1224,plain,(
% 4.47/1.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_relat_1(sK2) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1223,f747])).
% 4.47/1.00  fof(f1223,plain,(
% 4.47/1.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_relat_1(sK2) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(resolution,[],[f1158,f113])).
% 4.47/1.00  fof(f1158,plain,(
% 4.47/1.00    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1157,f754])).
% 4.47/1.00  fof(f754,plain,(
% 4.47/1.00    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(subsumption_resolution,[],[f750,f197])).
% 4.47/1.00  fof(f197,plain,(
% 4.47/1.00    ~v1_xboole_0(sK2) | spl6_8),
% 4.47/1.00    inference(avatar_component_clause,[],[f196])).
% 4.47/1.00  fof(f750,plain,(
% 4.47/1.00    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f720,f108])).
% 4.47/1.00  fof(f1157,plain,(
% 4.47/1.00    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f1156,f155])).
% 4.47/1.00  fof(f1156,plain,(
% 4.47/1.00    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f751,f721])).
% 4.47/1.00  fof(f751,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f720,f105])).
% 4.47/1.00  fof(f105,plain,(
% 4.47/1.00    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 4.47/1.00    inference(cnf_transformation,[],[f41])).
% 4.47/1.00  fof(f41,plain,(
% 4.47/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.47/1.00    inference(flattening,[],[f40])).
% 4.47/1.00  fof(f40,plain,(
% 4.47/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.47/1.00    inference(ennf_transformation,[],[f16])).
% 4.47/1.00  fof(f16,axiom,(
% 4.47/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 4.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 4.47/1.00  fof(f1240,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f1235])).
% 4.47/1.00  fof(f1235,plain,(
% 4.47/1.00    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v5_pre_topc(X8,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X9) | v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X9)) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl6_5 | spl6_8)),
% 4.47/1.00    inference(backward_demodulation,[],[f776,f1225])).
% 4.47/1.00  fof(f1210,plain,(
% 4.47/1.00    spl6_46),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1209])).
% 4.47/1.00  fof(f1209,plain,(
% 4.47/1.00    $false | spl6_46),
% 4.47/1.00    inference(subsumption_resolution,[],[f1208,f79])).
% 4.47/1.00  fof(f1208,plain,(
% 4.47/1.00    ~v2_pre_topc(sK1) | spl6_46),
% 4.47/1.00    inference(subsumption_resolution,[],[f1207,f80])).
% 4.47/1.00  fof(f1207,plain,(
% 4.47/1.00    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl6_46),
% 4.47/1.00    inference(resolution,[],[f1099,f97])).
% 4.47/1.00  fof(f1099,plain,(
% 4.47/1.00    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_46),
% 4.47/1.00    inference(avatar_component_clause,[],[f1097])).
% 4.47/1.00  fof(f1206,plain,(
% 4.47/1.00    ~spl6_5 | spl6_49),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1205])).
% 4.47/1.00  fof(f1205,plain,(
% 4.47/1.00    $false | (~spl6_5 | spl6_49)),
% 4.47/1.00    inference(subsumption_resolution,[],[f721,f1150])).
% 4.47/1.00  fof(f1150,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_49),
% 4.47/1.00    inference(avatar_component_clause,[],[f1148])).
% 4.47/1.00  fof(f1204,plain,(
% 4.47/1.00    ~spl6_2 | ~spl6_5 | spl6_48),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1203])).
% 4.47/1.00  fof(f1203,plain,(
% 4.47/1.00    $false | (~spl6_2 | ~spl6_5 | spl6_48)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1202,f1123])).
% 4.47/1.00  fof(f1123,plain,(
% 4.47/1.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_48),
% 4.47/1.00    inference(avatar_component_clause,[],[f1122])).
% 4.47/1.00  fof(f1202,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(forward_demodulation,[],[f1201,f87])).
% 4.47/1.00  fof(f1201,plain,(
% 4.47/1.00    v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(forward_demodulation,[],[f149,f717])).
% 4.47/1.00  fof(f1190,plain,(
% 4.47/1.00    ~spl6_5 | spl6_8 | spl6_15),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1189])).
% 4.47/1.00  fof(f1189,plain,(
% 4.47/1.00    $false | (~spl6_5 | spl6_8 | spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f316,f1158])).
% 4.47/1.00  fof(f316,plain,(
% 4.47/1.00    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | spl6_15),
% 4.47/1.00    inference(avatar_component_clause,[],[f315])).
% 4.47/1.00  fof(f315,plain,(
% 4.47/1.00    spl6_15 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 4.47/1.00  fof(f1187,plain,(
% 4.47/1.00    ~spl6_16 | spl6_33),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1186])).
% 4.47/1.00  fof(f1186,plain,(
% 4.47/1.00    $false | (~spl6_16 | spl6_33)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1172,f91])).
% 4.47/1.00  fof(f1172,plain,(
% 4.47/1.00    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl6_16 | spl6_33)),
% 4.47/1.00    inference(backward_demodulation,[],[f942,f321])).
% 4.47/1.00  fof(f942,plain,(
% 4.47/1.00    ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_relat_1(sK2)) | spl6_33),
% 4.47/1.00    inference(avatar_component_clause,[],[f940])).
% 4.47/1.00  fof(f940,plain,(
% 4.47/1.00    spl6_33 <=> r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_relat_1(sK2))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 4.47/1.00  fof(f1139,plain,(
% 4.47/1.00    ~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f1138])).
% 4.47/1.00  fof(f1138,plain,(
% 4.47/1.00    $false | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1137,f331])).
% 4.47/1.00  fof(f1137,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(forward_demodulation,[],[f1136,f818])).
% 4.47/1.00  fof(f818,plain,(
% 4.47/1.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f817,f175])).
% 4.47/1.00  fof(f817,plain,(
% 4.47/1.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_relat_1(sK2) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f816,f747])).
% 4.47/1.00  fof(f816,plain,(
% 4.47/1.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_relat_1(sK2) | ~spl6_15),
% 4.47/1.00    inference(resolution,[],[f317,f113])).
% 4.47/1.00  fof(f317,plain,(
% 4.47/1.00    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~spl6_15),
% 4.47/1.00    inference(avatar_component_clause,[],[f315])).
% 4.47/1.00  fof(f1136,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1135,f329])).
% 4.47/1.00  fof(f1135,plain,(
% 4.47/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(forward_demodulation,[],[f1134,f818])).
% 4.47/1.00  fof(f1134,plain,(
% 4.47/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1133,f823])).
% 4.47/1.00  fof(f823,plain,(
% 4.47/1.00    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(backward_demodulation,[],[f721,f818])).
% 4.47/1.00  fof(f1133,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(forward_demodulation,[],[f1132,f818])).
% 4.47/1.00  fof(f1132,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1131,f766])).
% 4.47/1.00  fof(f766,plain,(
% 4.47/1.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f765,f77])).
% 4.47/1.00  fof(f765,plain,(
% 4.47/1.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f756,f78])).
% 4.47/1.00  fof(f756,plain,(
% 4.47/1.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_5),
% 4.47/1.00    inference(superposition,[],[f97,f717])).
% 4.47/1.00  fof(f1131,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1130,f724])).
% 4.47/1.00  fof(f724,plain,(
% 4.47/1.00    l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_5),
% 4.47/1.00    inference(backward_demodulation,[],[f159,f717])).
% 4.47/1.00  fof(f1130,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1129,f79])).
% 4.47/1.00  fof(f1129,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1128,f80])).
% 4.47/1.00  fof(f1128,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1127,f155])).
% 4.47/1.00  fof(f1127,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1126,f863])).
% 4.47/1.00  fof(f863,plain,(
% 4.47/1.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(forward_demodulation,[],[f862,f87])).
% 4.47/1.00  fof(f862,plain,(
% 4.47/1.00    ~v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(forward_demodulation,[],[f150,f717])).
% 4.47/1.00  fof(f1126,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f744,f1118])).
% 4.47/1.00  fof(f1118,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1117,f79])).
% 4.47/1.00  fof(f1117,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK1) | (~spl6_1 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1116,f80])).
% 4.47/1.00  fof(f1116,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_1 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1106,f155])).
% 4.47/1.00  fof(f1106,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_1 | ~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1105,f145])).
% 4.47/1.00  fof(f1105,plain,(
% 4.47/1.00    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f1085,f331])).
% 4.47/1.00  fof(f1085,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(resolution,[],[f847,f329])).
% 4.47/1.00  fof(f847,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_1(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f846])).
% 4.47/1.00  fof(f846,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_1(X12) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(forward_demodulation,[],[f832,f818])).
% 4.47/1.00  fof(f832,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(duplicate_literal_removal,[],[f830])).
% 4.47/1.00  fof(f830,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl6_5 | ~spl6_15)),
% 4.47/1.00    inference(backward_demodulation,[],[f780,f818])).
% 4.47/1.00  fof(f780,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)))) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f779,f77])).
% 4.47/1.00  fof(f779,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)))) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | ~v2_pre_topc(sK0)) ) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f763,f78])).
% 4.47/1.00  fof(f763,plain,(
% 4.47/1.00    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)))) | ~v5_pre_topc(X12,sK0,X13) | v5_pre_topc(X12,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X13) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl6_5),
% 4.47/1.00    inference(superposition,[],[f140,f717])).
% 4.47/1.00  fof(f744,plain,(
% 4.47/1.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f720,f138])).
% 4.47/1.00  fof(f947,plain,(
% 4.47/1.00    ~spl6_33 | spl6_34 | ~spl6_5),
% 4.47/1.00    inference(avatar_split_clause,[],[f938,f183,f944,f940])).
% 4.47/1.00  fof(f938,plain,(
% 4.47/1.00    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_relat_1(sK2) | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_relat_1(sK2)) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f874,f117])).
% 4.47/1.00  fof(f874,plain,(
% 4.47/1.00    r1_tarski(k2_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f873,f175])).
% 4.47/1.00  fof(f873,plain,(
% 4.47/1.00    r1_tarski(k2_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f748,f106])).
% 4.47/1.00  fof(f748,plain,(
% 4.47/1.00    v5_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f720,f126])).
% 4.47/1.00  fof(f891,plain,(
% 4.47/1.00    ~spl6_5 | spl6_19),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f890])).
% 4.47/1.00  fof(f890,plain,(
% 4.47/1.00    $false | (~spl6_5 | spl6_19)),
% 4.47/1.00    inference(subsumption_resolution,[],[f889,f91])).
% 4.47/1.00  fof(f889,plain,(
% 4.47/1.00    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | (~spl6_5 | spl6_19)),
% 4.47/1.00    inference(resolution,[],[f733,f122])).
% 4.47/1.00  fof(f733,plain,(
% 4.47/1.00    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl6_5 | spl6_19)),
% 4.47/1.00    inference(backward_demodulation,[],[f463,f717])).
% 4.47/1.00  fof(f463,plain,(
% 4.47/1.00    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | spl6_19),
% 4.47/1.00    inference(avatar_component_clause,[],[f461])).
% 4.47/1.00  fof(f839,plain,(
% 4.47/1.00    ~spl6_5 | spl6_13 | ~spl6_15),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f838])).
% 4.47/1.00  fof(f838,plain,(
% 4.47/1.00    $false | (~spl6_5 | spl6_13 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f820,f329])).
% 4.47/1.00  fof(f820,plain,(
% 4.47/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl6_5 | spl6_13 | ~spl6_15)),
% 4.47/1.00    inference(backward_demodulation,[],[f306,f818])).
% 4.47/1.00  fof(f306,plain,(
% 4.47/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl6_13),
% 4.47/1.00    inference(avatar_component_clause,[],[f304])).
% 4.47/1.00  fof(f304,plain,(
% 4.47/1.00    spl6_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 4.47/1.00  fof(f837,plain,(
% 4.47/1.00    ~spl6_5 | spl6_12 | ~spl6_15),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f836])).
% 4.47/1.00  fof(f836,plain,(
% 4.47/1.00    $false | (~spl6_5 | spl6_12 | ~spl6_15)),
% 4.47/1.00    inference(subsumption_resolution,[],[f819,f331])).
% 4.47/1.00  fof(f819,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl6_5 | spl6_12 | ~spl6_15)),
% 4.47/1.00    inference(backward_demodulation,[],[f302,f818])).
% 4.47/1.00  fof(f302,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl6_12),
% 4.47/1.00    inference(avatar_component_clause,[],[f300])).
% 4.47/1.00  fof(f300,plain,(
% 4.47/1.00    spl6_12 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 4.47/1.00  fof(f476,plain,(
% 4.47/1.00    ~spl6_6 | spl6_17),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f475])).
% 4.47/1.00  fof(f475,plain,(
% 4.47/1.00    $false | (~spl6_6 | spl6_17)),
% 4.47/1.00    inference(subsumption_resolution,[],[f472,f455])).
% 4.47/1.00  fof(f455,plain,(
% 4.47/1.00    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_17),
% 4.47/1.00    inference(avatar_component_clause,[],[f453])).
% 4.47/1.00  fof(f472,plain,(
% 4.47/1.00    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_6),
% 4.47/1.00    inference(resolution,[],[f337,f109])).
% 4.47/1.00  fof(f337,plain,(
% 4.47/1.00    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~spl6_6),
% 4.47/1.00    inference(backward_demodulation,[],[f158,f189])).
% 4.47/1.00  fof(f353,plain,(
% 4.47/1.00    ~spl6_6 | spl6_10),
% 4.47/1.00    inference(avatar_contradiction_clause,[],[f352])).
% 4.47/1.00  fof(f352,plain,(
% 4.47/1.00    $false | (~spl6_6 | spl6_10)),
% 4.47/1.00    inference(subsumption_resolution,[],[f345,f91])).
% 4.47/1.00  fof(f345,plain,(
% 4.47/1.00    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl6_6 | spl6_10)),
% 4.47/1.00    inference(backward_demodulation,[],[f249,f189])).
% 4.47/1.00  fof(f249,plain,(
% 4.47/1.00    ~r1_tarski(u1_struct_0(sK1),k2_relat_1(sK2)) | spl6_10),
% 4.47/1.00    inference(avatar_component_clause,[],[f247])).
% 4.47/1.00  fof(f247,plain,(
% 4.47/1.00    spl6_10 <=> r1_tarski(u1_struct_0(sK1),k2_relat_1(sK2))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 4.47/1.00  fof(f322,plain,(
% 4.47/1.00    spl6_15 | spl6_16 | ~spl6_5),
% 4.47/1.00    inference(avatar_split_clause,[],[f313,f183,f319,f315])).
% 4.47/1.00  fof(f313,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f312,f155])).
% 4.47/1.00  fof(f312,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_funct_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f284,f218])).
% 4.47/1.00  fof(f218,plain,(
% 4.47/1.00    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 4.47/1.00    inference(backward_demodulation,[],[f154,f214])).
% 4.47/1.00  fof(f214,plain,(
% 4.47/1.00    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f213,f175])).
% 4.47/1.00  fof(f213,plain,(
% 4.47/1.00    u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f212,f173])).
% 4.47/1.00  fof(f212,plain,(
% 4.47/1.00    u1_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f185,f113])).
% 4.47/1.00  fof(f284,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f217,f142])).
% 4.47/1.00  fof(f217,plain,(
% 4.47/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_5),
% 4.47/1.00    inference(backward_demodulation,[],[f153,f214])).
% 4.47/1.00  fof(f311,plain,(
% 4.47/1.00    ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_2 | ~spl6_5),
% 4.47/1.00    inference(avatar_split_clause,[],[f298,f183,f148,f308,f304,f300])).
% 4.47/1.00  fof(f298,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f297,f265])).
% 4.47/1.00  fof(f265,plain,(
% 4.47/1.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f264,f77])).
% 4.47/1.00  fof(f264,plain,(
% 4.47/1.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | ~spl6_5),
% 4.47/1.00    inference(subsumption_resolution,[],[f255,f78])).
% 4.47/1.00  fof(f255,plain,(
% 4.47/1.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_5),
% 4.47/1.00    inference(superposition,[],[f97,f214])).
% 4.47/1.00  fof(f297,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f296,f221])).
% 4.47/1.00  fof(f221,plain,(
% 4.47/1.00    l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_5),
% 4.47/1.00    inference(backward_demodulation,[],[f159,f214])).
% 4.47/1.00  fof(f296,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f295,f79])).
% 4.47/1.00  fof(f295,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f294,f80])).
% 4.47/1.00  fof(f294,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f293,f155])).
% 4.47/1.00  fof(f293,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f292,f218])).
% 4.47/1.00  fof(f292,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(subsumption_resolution,[],[f283,f219])).
% 4.47/1.00  fof(f219,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_5)),
% 4.47/1.00    inference(backward_demodulation,[],[f156,f214])).
% 4.47/1.00  fof(f156,plain,(
% 4.47/1.00    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_2),
% 4.47/1.00    inference(forward_demodulation,[],[f149,f87])).
% 4.47/1.00  fof(f283,plain,(
% 4.47/1.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_5),
% 4.47/1.00    inference(resolution,[],[f217,f137])).
% 4.47/1.00  fof(f254,plain,(
% 4.47/1.00    ~spl6_10 | spl6_11),
% 4.47/1.00    inference(avatar_split_clause,[],[f245,f251,f247])).
% 4.47/1.00  fof(f245,plain,(
% 4.47/1.00    u1_struct_0(sK1) = k2_relat_1(sK2) | ~r1_tarski(u1_struct_0(sK1),k2_relat_1(sK2))),
% 4.47/1.00    inference(resolution,[],[f211,f117])).
% 4.47/1.00  fof(f202,plain,(
% 4.47/1.00    spl6_7 | spl6_5),
% 4.47/1.00    inference(avatar_split_clause,[],[f201,f183,f192])).
% 4.47/1.00  fof(f192,plain,(
% 4.47/1.00    spl6_7 <=> v1_xboole_0(u1_struct_0(sK1))),
% 4.47/1.00    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 4.47/1.00  fof(f201,plain,(
% 4.47/1.00    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 4.47/1.00    inference(subsumption_resolution,[],[f200,f155])).
% 4.47/1.00  fof(f200,plain,(
% 4.47/1.00    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 4.47/1.00    inference(subsumption_resolution,[],[f177,f82])).
% 4.47/1.00  fof(f177,plain,(
% 4.47/1.00    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 4.47/1.00    inference(resolution,[],[f83,f105])).
% 4.47/1.00  fof(f199,plain,(
% 4.47/1.00    ~spl6_7 | spl6_8),
% 4.47/1.00    inference(avatar_split_clause,[],[f176,f196,f192])).
% 4.47/1.00  fof(f176,plain,(
% 4.47/1.00    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(sK1))),
% 4.47/1.00    inference(resolution,[],[f83,f108])).
% 4.47/1.00  fof(f190,plain,(
% 4.47/1.00    spl6_5 | spl6_6),
% 4.47/1.00    inference(avatar_split_clause,[],[f181,f187,f183])).
% 4.47/1.00  fof(f181,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0))),
% 4.47/1.00    inference(subsumption_resolution,[],[f180,f155])).
% 4.47/1.00  fof(f180,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 4.47/1.00    inference(subsumption_resolution,[],[f172,f82])).
% 4.47/1.00  fof(f172,plain,(
% 4.47/1.00    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 4.47/1.00    inference(resolution,[],[f83,f142])).
% 4.47/1.00  fof(f152,plain,(
% 4.47/1.00    spl6_1 | spl6_2),
% 4.47/1.00    inference(avatar_split_clause,[],[f88,f148,f144])).
% 4.47/1.00  fof(f88,plain,(
% 4.47/1.00    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 4.47/1.00    inference(cnf_transformation,[],[f61])).
% 4.47/1.00  fof(f151,plain,(
% 4.47/1.00    ~spl6_1 | ~spl6_2),
% 4.47/1.00    inference(avatar_split_clause,[],[f89,f148,f144])).
% 4.47/1.00  fof(f89,plain,(
% 4.47/1.00    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 4.47/1.00    inference(cnf_transformation,[],[f61])).
% 4.47/1.00  % SZS output end Proof for theBenchmark
% 4.47/1.00  % (30781)------------------------------
% 4.47/1.00  % (30781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.00  % (30781)Termination reason: Refutation
% 4.47/1.00  
% 4.47/1.00  % (30781)Memory used [KB]: 13560
% 4.47/1.00  % (30781)Time elapsed: 0.595 s
% 4.47/1.00  % (30781)------------------------------
% 4.47/1.00  % (30781)------------------------------
% 4.47/1.01  % (30771)Success in time 0.639 s
%------------------------------------------------------------------------------
