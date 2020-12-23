%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:34 EST 2020

% Result     : Theorem 4.75s
% Output     : Refutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  367 (2627 expanded)
%              Number of leaves         :   52 ( 946 expanded)
%              Depth                    :   22
%              Number of atoms          : 1672 (29212 expanded)
%              Number of equality atoms :   76 (2395 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10990,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f210,f211,f1551,f1649,f1888,f1892,f5786,f5834,f5848,f5855,f7262,f8742,f9535,f9540,f9697,f9739,f9835,f9898,f9901,f10021,f10029,f10071,f10077,f10283,f10363,f10376,f10380,f10467,f10492,f10496,f10826,f10827,f10858,f10917,f10944,f10956,f10981])).

fof(f10981,plain,
    ( ~ spl16_6
    | ~ spl16_9
    | spl16_48 ),
    inference(avatar_split_clause,[],[f8313,f1636,f288,f274])).

fof(f274,plain,
    ( spl16_6
  <=> v1_xboole_0(u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f288,plain,
    ( spl16_9
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f1636,plain,
    ( spl16_48
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).

fof(f8313,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | spl16_48 ),
    inference(superposition,[],[f1638,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f196,f140])).

fof(f140,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f196,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1638,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | spl16_48 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f10956,plain,
    ( spl16_329
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f10955,f207,f9756])).

fof(f9756,plain,
    ( spl16_329
  <=> v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_329])])).

fof(f207,plain,
    ( spl16_2
  <=> v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f10955,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_2 ),
    inference(forward_demodulation,[],[f208,f117])).

fof(f117,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
      | ~ v5_pre_topc(sK7,sK5,sK6) )
    & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
      | v5_pre_topc(sK7,sK5,sK6) )
    & sK7 = sK8
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f66,f70,f69,f68,f67])).

fof(f67,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK5,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK5,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK5,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK5,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
                | ~ v5_pre_topc(X2,sK5,sK6) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
                | v5_pre_topc(X2,sK5,sK6) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
          & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
              | ~ v5_pre_topc(X2,sK5,sK6) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
              | v5_pre_topc(X2,sK5,sK6) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
            | ~ v5_pre_topc(sK7,sK5,sK6) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
            | v5_pre_topc(sK7,sK5,sK6) )
          & sK7 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
          | ~ v5_pre_topc(sK7,sK5,sK6) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
          | v5_pre_topc(sK7,sK5,sK6) )
        & sK7 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
        | ~ v5_pre_topc(sK7,sK5,sK6) )
      & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
        | v5_pre_topc(sK7,sK5,sK6) )
      & sK7 = sK8
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
      & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f208,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f207])).

fof(f10944,plain,
    ( spl16_4
    | ~ spl16_33 ),
    inference(avatar_split_clause,[],[f5954,f722,f243])).

fof(f243,plain,
    ( spl16_4
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f722,plain,
    ( spl16_33
  <=> ! [X11] : ~ r2_hidden(X11,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_33])])).

fof(f5954,plain,
    ( v1_xboole_0(sK7)
    | ~ spl16_33 ),
    inference(resolution,[],[f723,f148])).

fof(f148,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK12(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f87,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK12(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
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

fof(f723,plain,
    ( ! [X11] : ~ r2_hidden(X11,sK7)
    | ~ spl16_33 ),
    inference(avatar_component_clause,[],[f722])).

fof(f10917,plain,
    ( spl16_124
    | ~ spl16_139 ),
    inference(avatar_split_clause,[],[f8228,f5784,f5529])).

fof(f5529,plain,
    ( spl16_124
  <=> ! [X4] :
        ( ~ v4_relat_1(sK7,X4)
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_124])])).

fof(f5784,plain,
    ( spl16_139
  <=> ! [X4] :
        ( ~ v4_relat_1(sK7,X4)
        | r2_hidden(sK12(u1_struct_0(sK5)),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_139])])).

fof(f8228,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(sK7,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl16_139 ),
    inference(resolution,[],[f5785,f147])).

fof(f147,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f5785,plain,
    ( ! [X4] :
        ( r2_hidden(sK12(u1_struct_0(sK5)),X4)
        | ~ v4_relat_1(sK7,X4) )
    | ~ spl16_139 ),
    inference(avatar_component_clause,[],[f5784])).

fof(f10858,plain,
    ( spl16_6
    | spl16_113 ),
    inference(avatar_split_clause,[],[f10857,f5306,f274])).

fof(f5306,plain,
    ( spl16_113
  <=> v1_partfun1(sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_113])])).

fof(f10857,plain,
    ( v1_partfun1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f10856,f111])).

fof(f111,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f10856,plain,
    ( ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f6408,f112])).

fof(f112,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f71])).

fof(f6408,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[],[f113,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f113,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f10827,plain,
    ( ~ spl16_47
    | spl16_1
    | ~ spl16_49
    | ~ spl16_48 ),
    inference(avatar_split_clause,[],[f10360,f1636,f1640,f203,f1632])).

fof(f1632,plain,
    ( spl16_47
  <=> v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_47])])).

fof(f203,plain,
    ( spl16_1
  <=> v5_pre_topc(sK7,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f1640,plain,
    ( spl16_49
  <=> v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_49])])).

fof(f10360,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10359,f107])).

fof(f107,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f10359,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10358,f108])).

fof(f108,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f10358,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10357,f109])).

fof(f109,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f10357,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10356,f110])).

fof(f110,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f10356,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10355,f112])).

fof(f10355,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10354,f113])).

fof(f10354,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10183,f111])).

fof(f10183,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(resolution,[],[f1637,f199])).

fof(f199,plain,(
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
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
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
    inference(equality_resolution,[],[f146])).

fof(f146,plain,(
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
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f1637,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ spl16_48 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f10826,plain,
    ( ~ spl16_47
    | spl16_49
    | ~ spl16_1
    | ~ spl16_48 ),
    inference(avatar_split_clause,[],[f10370,f1636,f203,f1640,f1632])).

fof(f10370,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10369,f107])).

fof(f10369,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10368,f108])).

fof(f10368,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10367,f109])).

fof(f10367,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10366,f110])).

fof(f10366,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10365,f112])).

fof(f10365,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10364,f113])).

fof(f10364,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f10184,f111])).

fof(f10184,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_48 ),
    inference(resolution,[],[f1637,f198])).

fof(f198,plain,(
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
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
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
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
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
    inference(cnf_transformation,[],[f85])).

fof(f10496,plain,
    ( ~ spl16_6
    | spl16_9 ),
    inference(avatar_split_clause,[],[f6422,f288,f274])).

fof(f6422,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(superposition,[],[f113,f216])).

fof(f10492,plain,
    ( ~ spl16_6
    | spl16_149 ),
    inference(avatar_split_clause,[],[f7393,f5867,f274])).

fof(f5867,plain,
    ( spl16_149
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_149])])).

fof(f7393,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | spl16_149 ),
    inference(duplicate_literal_removal,[],[f7392])).

fof(f7392,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | spl16_149 ),
    inference(superposition,[],[f5869,f216])).

fof(f5869,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))
    | spl16_149 ),
    inference(avatar_component_clause,[],[f5867])).

fof(f10467,plain,
    ( ~ spl16_6
    | spl16_33 ),
    inference(avatar_split_clause,[],[f10466,f722,f274])).

fof(f10466,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK7)
      | ~ v1_xboole_0(u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f8812,f147])).

fof(f8812,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK6))
      | ~ r2_hidden(X1,sK7)
      | ~ v1_xboole_0(u1_struct_0(sK6)) ) ),
    inference(superposition,[],[f630,f216])).

fof(f630,plain,(
    ! [X10] :
      ( r2_hidden(X10,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))
      | ~ r2_hidden(X10,sK7) ) ),
    inference(resolution,[],[f170,f254])).

fof(f254,plain,(
    r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) ),
    inference(resolution,[],[f173,f113])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f170,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK14(X0,X1),X1)
          & r2_hidden(sK14(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f99,f100])).

fof(f100,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK14(X0,X1),X1)
        & r2_hidden(sK14(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
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

fof(f10380,plain,
    ( ~ spl16_4
    | spl16_13 ),
    inference(avatar_split_clause,[],[f10097,f307,f243])).

fof(f307,plain,
    ( spl16_13
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f10097,plain,
    ( ~ v1_xboole_0(sK7)
    | spl16_13 ),
    inference(resolution,[],[f308,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f121,f140])).

fof(f121,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f308,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))
    | spl16_13 ),
    inference(avatar_component_clause,[],[f307])).

fof(f10376,plain,
    ( ~ spl16_329
    | spl16_2 ),
    inference(avatar_split_clause,[],[f10375,f207,f9756])).

fof(f10375,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl16_2 ),
    inference(forward_demodulation,[],[f209,f117])).

fof(f209,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl16_2 ),
    inference(avatar_component_clause,[],[f207])).

fof(f10363,plain,
    ( spl16_1
    | ~ spl16_49
    | ~ spl16_48
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(avatar_split_clause,[],[f10362,f7266,f5306,f1636,f1640,f203])).

fof(f7266,plain,
    ( spl16_233
  <=> v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_233])])).

fof(f10362,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ spl16_48
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(subsumption_resolution,[],[f10361,f112])).

fof(f10361,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ spl16_48
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(forward_demodulation,[],[f10360,f10180])).

fof(f10180,plain,
    ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(subsumption_resolution,[],[f10179,f669])).

fof(f669,plain,(
    v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f185,f225])).

fof(f225,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(forward_demodulation,[],[f116,f117])).

fof(f116,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(cnf_transformation,[],[f71])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f10179,plain,
    ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(subsumption_resolution,[],[f10176,f668])).

fof(f668,plain,(
    v4_relat_1(sK7,u1_struct_0(sK5)) ),
    inference(resolution,[],[f185,f113])).

fof(f10176,plain,
    ( ~ v4_relat_1(sK7,u1_struct_0(sK5))
    | u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(resolution,[],[f7875,f7851])).

fof(f7851,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,u1_struct_0(sK5))
        | u1_struct_0(sK5) = X7
        | ~ v4_relat_1(sK7,X7) )
    | ~ spl16_113 ),
    inference(resolution,[],[f6083,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
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

fof(f6083,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(sK5),X0)
        | ~ v4_relat_1(sK7,X0) )
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f6082,f668])).

fof(f6082,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | r1_tarski(u1_struct_0(sK5),X0)
        | ~ v4_relat_1(sK7,u1_struct_0(sK5)) )
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f6078,f407])).

fof(f407,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f184,f113])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f6078,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | ~ v1_relat_1(sK7)
        | r1_tarski(u1_struct_0(sK5),X0)
        | ~ v4_relat_1(sK7,u1_struct_0(sK5)) )
    | ~ spl16_113 ),
    inference(resolution,[],[f5307,f1104])).

fof(f1104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X1,X2)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1094])).

fof(f1094,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f156,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f156,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f5307,plain,
    ( v1_partfun1(sK7,u1_struct_0(sK5))
    | ~ spl16_113 ),
    inference(avatar_component_clause,[],[f5306])).

fof(f7875,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0)
        | ~ v4_relat_1(sK7,X0) )
    | ~ spl16_233 ),
    inference(subsumption_resolution,[],[f7874,f669])).

fof(f7874,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0)
        | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) )
    | ~ spl16_233 ),
    inference(subsumption_resolution,[],[f7870,f407])).

fof(f7870,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | ~ v1_relat_1(sK7)
        | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0)
        | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) )
    | ~ spl16_233 ),
    inference(resolution,[],[f7268,f1104])).

fof(f7268,plain,
    ( v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ spl16_233 ),
    inference(avatar_component_clause,[],[f7266])).

fof(f10283,plain,
    ( spl16_47
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(avatar_contradiction_clause,[],[f10282])).

fof(f10282,plain,
    ( $false
    | spl16_47
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(subsumption_resolution,[],[f10218,f112])).

fof(f10218,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | spl16_47
    | ~ spl16_113
    | ~ spl16_233 ),
    inference(backward_demodulation,[],[f1634,f10180])).

fof(f1634,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | spl16_47 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f10077,plain,
    ( ~ spl16_42
    | ~ spl16_325
    | spl16_329
    | ~ spl16_44
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(avatar_split_clause,[],[f10076,f1538,f1530,f1526,f1542,f9756,f9701,f1534])).

fof(f1534,plain,
    ( spl16_42
  <=> v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).

fof(f9701,plain,
    ( spl16_325
  <=> v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_325])])).

fof(f1542,plain,
    ( spl16_44
  <=> v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).

fof(f1526,plain,
    ( spl16_40
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).

fof(f1530,plain,
    ( spl16_41
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).

% (15702)Termination reason: Time limit

fof(f1538,plain,
    ( spl16_43
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_43])])).

% (15702)Memory used [KB]: 10618
% (15702)Time elapsed: 0.622 s
% (15702)------------------------------
% (15702)------------------------------
fof(f10076,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10075,f107])).

fof(f10075,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(sK5)
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10074,f108])).

fof(f10074,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10073,f1527])).

fof(f1527,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_40 ),
    inference(avatar_component_clause,[],[f1526])).

% (15735)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
fof(f10073,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10072,f1531])).

fof(f1531,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_41 ),
    inference(avatar_component_clause,[],[f1530])).

fof(f10072,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f9766,f1539])).

fof(f1539,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ spl16_43 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f9766,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f7231,f111])).

fof(f7231,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f225,f198])).

fof(f10071,plain,
    ( ~ spl16_42
    | ~ spl16_325
    | spl16_44
    | ~ spl16_329
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(avatar_split_clause,[],[f10070,f1538,f1530,f1526,f9756,f1542,f9701,f1534])).

fof(f10070,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10069,f107])).

fof(f10069,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(sK5)
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10068,f108])).

fof(f10068,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_40
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10067,f1527])).

fof(f10067,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_41
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10066,f1531])).

fof(f10066,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f9773,f1539])).

fof(f9773,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f7230,f111])).

fof(f7230,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f225,f199])).

fof(f10029,plain,
    ( ~ spl16_42
    | spl16_44
    | ~ spl16_1
    | ~ spl16_43 ),
    inference(avatar_split_clause,[],[f10028,f1538,f203,f1542,f1534])).

fof(f10028,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10027,f107])).

fof(f10027,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10026,f108])).

fof(f10026,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10025,f109])).

fof(f10025,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10024,f110])).

fof(f10024,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10023,f112])).

fof(f10023,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10022,f113])).

fof(f10022,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f9957,f111])).

fof(f9957,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(resolution,[],[f1539,f200])).

fof(f200,plain,(
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
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
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
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
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
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f10021,plain,
    ( ~ spl16_42
    | spl16_1
    | ~ spl16_44
    | ~ spl16_43 ),
    inference(avatar_split_clause,[],[f10020,f1538,f1542,f203,f1534])).

fof(f10020,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10019,f107])).

fof(f10019,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10018,f108])).

fof(f10018,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10017,f109])).

fof(f10017,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10016,f110])).

fof(f10016,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10015,f112])).

fof(f10015,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f10014,f113])).

fof(f10014,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(subsumption_resolution,[],[f9956,f111])).

fof(f9956,plain,
    ( ~ v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ spl16_43 ),
    inference(resolution,[],[f1539,f201])).

fof(f201,plain,(
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
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
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
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
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
    inference(cnf_transformation,[],[f84])).

fof(f9901,plain,
    ( spl16_233
    | ~ spl16_325
    | spl16_10 ),
    inference(avatar_split_clause,[],[f9900,f293,f9701,f7266])).

fof(f293,plain,
    ( spl16_10
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f9900,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | spl16_10 ),
    inference(subsumption_resolution,[],[f9899,f295])).

fof(f295,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | spl16_10 ),
    inference(avatar_component_clause,[],[f293])).

fof(f9899,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(subsumption_resolution,[],[f9858,f111])).

fof(f9858,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(resolution,[],[f225,f155])).

fof(f9898,plain,
    ( ~ spl16_47
    | ~ spl16_48
    | ~ spl16_325
    | spl16_329
    | ~ spl16_49
    | ~ spl16_45
    | ~ spl16_46 ),
    inference(avatar_split_clause,[],[f9897,f1628,f1624,f1640,f9756,f9701,f1636,f1632])).

fof(f1624,plain,
    ( spl16_45
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f1628,plain,
    ( spl16_46
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_46])])).

fof(f9897,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ spl16_45
    | ~ spl16_46 ),
    inference(subsumption_resolution,[],[f9896,f1625])).

fof(f1625,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_45 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f9896,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_46 ),
    inference(subsumption_resolution,[],[f9895,f1629])).

fof(f1629,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_46 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f9895,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f9894,f109])).

fof(f9894,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f9893,f110])).

fof(f9893,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f9857,f111])).

fof(f9857,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(resolution,[],[f225,f200])).

fof(f9835,plain,(
    spl16_325 ),
    inference(avatar_split_clause,[],[f219,f9701])).

fof(f219,plain,(
    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(forward_demodulation,[],[f115,f117])).

fof(f115,plain,(
    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f9739,plain,
    ( ~ spl16_10
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f9738,f5529,f293])).

fof(f9738,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ spl16_124 ),
    inference(subsumption_resolution,[],[f1455,f5626])).

fof(f5626,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK7,X4)
        | ~ v1_xboole_0(X4) )
    | ~ spl16_124 ),
    inference(duplicate_literal_removal,[],[f5620])).

fof(f5620,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | ~ r1_tarski(sK7,X4)
        | ~ v1_xboole_0(X4) )
    | ~ spl16_124 ),
    inference(resolution,[],[f5530,f1907])).

fof(f1907,plain,(
    ! [X4,X2] :
      ( v4_relat_1(X4,X2)
      | ~ r1_tarski(X4,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(superposition,[],[f665,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f197,f140])).

fof(f197,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f665,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f185,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f5530,plain,
    ( ! [X4] :
        ( ~ v4_relat_1(sK7,X4)
        | ~ v1_xboole_0(X4) )
    | ~ spl16_124 ),
    inference(avatar_component_clause,[],[f5529])).

fof(f1455,plain,
    ( r1_tarski(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(superposition,[],[f255,f216])).

fof(f255,plain,(
    r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) ),
    inference(resolution,[],[f173,f225])).

fof(f9697,plain,
    ( ~ spl16_10
    | ~ spl16_13
    | spl16_43 ),
    inference(avatar_split_clause,[],[f8280,f1538,f307,f293])).

fof(f8280,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | spl16_43 ),
    inference(superposition,[],[f1540,f216])).

fof(f1540,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | spl16_43 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f9540,plain,
    ( spl16_10
    | spl16_48
    | ~ spl16_113 ),
    inference(avatar_contradiction_clause,[],[f9539])).

fof(f9539,plain,
    ( $false
    | spl16_10
    | spl16_48
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f9476,f254])).

fof(f9476,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))
    | spl16_10
    | spl16_48
    | ~ spl16_113 ),
    inference(backward_demodulation,[],[f8308,f9427])).

fof(f9427,plain,
    ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | spl16_10
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f9426,f668])).

fof(f9426,plain,
    ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v4_relat_1(sK7,u1_struct_0(sK5))
    | spl16_10
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f9401,f669])).

fof(f9401,plain,
    ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v4_relat_1(sK7,u1_struct_0(sK5))
    | spl16_10
    | ~ spl16_113 ),
    inference(resolution,[],[f7851,f5127])).

fof(f5127,plain,
    ( ! [X16] :
        ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X16)
        | ~ v4_relat_1(sK7,X16) )
    | spl16_10 ),
    inference(subsumption_resolution,[],[f5126,f669])).

fof(f5126,plain,
    ( ! [X16] :
        ( ~ v4_relat_1(sK7,X16)
        | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X16)
        | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) )
    | spl16_10 ),
    inference(subsumption_resolution,[],[f5120,f407])).

fof(f5120,plain,
    ( ! [X16] :
        ( ~ v4_relat_1(sK7,X16)
        | ~ v1_relat_1(sK7)
        | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X16)
        | ~ v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) )
    | spl16_10 ),
    inference(resolution,[],[f1104,f1160])).

fof(f1160,plain,
    ( v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | spl16_10 ),
    inference(subsumption_resolution,[],[f1159,f295])).

fof(f1159,plain,
    ( v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(subsumption_resolution,[],[f1158,f111])).

fof(f1158,plain,
    ( ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(subsumption_resolution,[],[f1142,f219])).

fof(f1142,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(resolution,[],[f155,f225])).

fof(f8308,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
    | spl16_48 ),
    inference(resolution,[],[f1638,f174])).

fof(f9535,plain,
    ( spl16_10
    | spl16_43
    | ~ spl16_113 ),
    inference(avatar_contradiction_clause,[],[f9534])).

fof(f9534,plain,
    ( $false
    | spl16_10
    | spl16_43
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f9458,f8275])).

fof(f8275,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))
    | spl16_43 ),
    inference(resolution,[],[f1540,f174])).

fof(f9458,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))
    | spl16_10
    | ~ spl16_113 ),
    inference(backward_demodulation,[],[f255,f9427])).

fof(f8742,plain,
    ( ~ spl16_149
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f8731,f5529,f5867])).

fof(f8731,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl16_124 ),
    inference(resolution,[],[f254,f5626])).

fof(f7262,plain,
    ( ~ spl16_45
    | ~ spl16_46
    | ~ spl16_47
    | ~ spl16_48
    | spl16_49
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f7261,f207,f1640,f1636,f1632,f1628,f1624])).

fof(f7261,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f7260,f109])).

fof(f7260,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f7259,f110])).

fof(f7259,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f7258,f111])).

fof(f7258,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f7257,f219])).

fof(f7257,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f7232,f218])).

fof(f218,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl16_2 ),
    inference(forward_demodulation,[],[f208,f117])).

fof(f7232,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(resolution,[],[f225,f201])).

fof(f5855,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | spl16_47 ),
    inference(avatar_split_clause,[],[f2546,f1632,f274,f243])).

fof(f2546,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ v1_xboole_0(sK7)
    | spl16_47 ),
    inference(resolution,[],[f1087,f1634])).

fof(f1087,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f1063,f140])).

fof(f1063,plain,(
    ! [X10,X11] :
      ( v1_funct_2(k1_xboole_0,X10,X11)
      | ~ v1_xboole_0(X11) ) ),
    inference(superposition,[],[f183,f1011])).

fof(f1011,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK15(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f926,f564])).

fof(f564,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f169,f256])).

fof(f256,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f173,f121])).

fof(f926,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(sK15(X5,X4),X6)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f641,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f641,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(X23,sK15(X24,X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(subsumption_resolution,[],[f637,f147])).

fof(f637,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(X23,sK15(X24,X25))
      | r2_hidden(X23,X25)
      | ~ v1_xboole_0(X25) ) ),
    inference(resolution,[],[f170,f496])).

fof(f496,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK15(X3,X4),X4)
      | ~ v1_xboole_0(X4) ) ),
    inference(superposition,[],[f397,f216])).

fof(f397,plain,(
    ! [X0,X1] : r1_tarski(sK15(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f178,f173])).

fof(f178,plain,(
    ! [X0,X1] : m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK15(X0,X1),X0,X1)
      & v1_funct_1(sK15(X0,X1))
      & v5_relat_1(sK15(X0,X1),X1)
      & v4_relat_1(sK15(X0,X1),X0)
      & v1_relat_1(sK15(X0,X1))
      & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f19,f105])).

fof(f105,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK15(X0,X1),X0,X1)
        & v1_funct_1(sK15(X0,X1))
        & v5_relat_1(sK15(X0,X1),X1)
        & v4_relat_1(sK15(X0,X1),X0)
        & v1_relat_1(sK15(X0,X1))
        & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f183,plain,(
    ! [X0,X1] : v1_funct_2(sK15(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f106])).

fof(f5848,plain,
    ( ~ spl16_4
    | ~ spl16_14
    | spl16_42 ),
    inference(avatar_split_clause,[],[f2542,f1534,f325,f243])).

fof(f325,plain,
    ( spl16_14
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).

fof(f2542,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ v1_xboole_0(sK7)
    | spl16_42 ),
    inference(resolution,[],[f1055,f1536])).

fof(f1536,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | spl16_42 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1055,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f1031,f140])).

fof(f1031,plain,(
    ! [X10,X11] :
      ( v1_funct_2(k1_xboole_0,X10,X11)
      | ~ v1_xboole_0(X10) ) ),
    inference(superposition,[],[f183,f998])).

fof(f998,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK15(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f910,f564])).

fof(f910,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(sK15(X4,X5),X6)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f640,f171])).

fof(f640,plain,(
    ! [X21,X22,X20] :
      ( ~ r2_hidden(X20,sK15(X21,X22))
      | ~ v1_xboole_0(X21) ) ),
    inference(subsumption_resolution,[],[f636,f147])).

fof(f636,plain,(
    ! [X21,X22,X20] :
      ( ~ r2_hidden(X20,sK15(X21,X22))
      | r2_hidden(X20,X21)
      | ~ v1_xboole_0(X21) ) ),
    inference(resolution,[],[f170,f495])).

fof(f495,plain,(
    ! [X2,X1] :
      ( r1_tarski(sK15(X1,X2),X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f397,f217])).

fof(f5834,plain,
    ( ~ spl16_14
    | spl16_33 ),
    inference(avatar_split_clause,[],[f5833,f722,f325])).

fof(f5833,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | ~ v1_xboole_0(u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f644,f147])).

fof(f644,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK5))
      | ~ r2_hidden(X0,sK7)
      | ~ v1_xboole_0(u1_struct_0(sK5)) ) ),
    inference(superposition,[],[f630,f217])).

fof(f5786,plain,
    ( spl16_14
    | spl16_139
    | ~ spl16_113 ),
    inference(avatar_split_clause,[],[f5715,f5306,f5784,f325])).

fof(f5715,plain,
    ( ! [X4] :
        ( ~ v4_relat_1(sK7,X4)
        | r2_hidden(sK12(u1_struct_0(sK5)),X4)
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl16_113 ),
    inference(resolution,[],[f5484,f148])).

fof(f5484,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,u1_struct_0(sK5))
        | ~ v4_relat_1(sK7,X5)
        | r2_hidden(X6,X5) )
    | ~ spl16_113 ),
    inference(resolution,[],[f5386,f170])).

fof(f5386,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(sK5),X0)
        | ~ v4_relat_1(sK7,X0) )
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f5385,f668])).

fof(f5385,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | r1_tarski(u1_struct_0(sK5),X0)
        | ~ v4_relat_1(sK7,u1_struct_0(sK5)) )
    | ~ spl16_113 ),
    inference(subsumption_resolution,[],[f5381,f407])).

fof(f5381,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | ~ v1_relat_1(sK7)
        | r1_tarski(u1_struct_0(sK5),X0)
        | ~ v4_relat_1(sK7,u1_struct_0(sK5)) )
    | ~ spl16_113 ),
    inference(resolution,[],[f5307,f1104])).

fof(f1892,plain,(
    spl16_46 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | spl16_46 ),
    inference(subsumption_resolution,[],[f1889,f108])).

fof(f1889,plain,
    ( ~ l1_pre_topc(sK5)
    | spl16_46 ),
    inference(resolution,[],[f1884,f443])).

fof(f443,plain,(
    ! [X0] :
      ( r1_tarski(u1_pre_topc(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f122,f173])).

fof(f122,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1884,plain,
    ( ~ r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | spl16_46 ),
    inference(resolution,[],[f533,f1630])).

fof(f1630,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | spl16_46 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f533,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ r1_tarski(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f160,f174])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f1888,plain,(
    spl16_41 ),
    inference(avatar_contradiction_clause,[],[f1887])).

fof(f1887,plain,
    ( $false
    | spl16_41 ),
    inference(subsumption_resolution,[],[f1885,f110])).

fof(f1885,plain,
    ( ~ l1_pre_topc(sK6)
    | spl16_41 ),
    inference(resolution,[],[f1883,f443])).

fof(f1883,plain,
    ( ~ r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl16_41 ),
    inference(resolution,[],[f533,f1532])).

fof(f1532,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl16_41 ),
    inference(avatar_component_clause,[],[f1530])).

fof(f1649,plain,(
    spl16_45 ),
    inference(avatar_contradiction_clause,[],[f1648])).

fof(f1648,plain,
    ( $false
    | spl16_45 ),
    inference(subsumption_resolution,[],[f1647,f107])).

fof(f1647,plain,
    ( ~ v2_pre_topc(sK5)
    | spl16_45 ),
    inference(subsumption_resolution,[],[f1646,f108])).

fof(f1646,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | spl16_45 ),
    inference(resolution,[],[f1626,f142])).

fof(f142,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f1626,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | spl16_45 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f1551,plain,(
    spl16_40 ),
    inference(avatar_contradiction_clause,[],[f1550])).

fof(f1550,plain,
    ( $false
    | spl16_40 ),
    inference(subsumption_resolution,[],[f1549,f109])).

fof(f1549,plain,
    ( ~ v2_pre_topc(sK6)
    | spl16_40 ),
    inference(subsumption_resolution,[],[f1548,f110])).

fof(f1548,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl16_40 ),
    inference(resolution,[],[f1528,f142])).

fof(f1528,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl16_40 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f211,plain,
    ( spl16_1
    | spl16_2 ),
    inference(avatar_split_clause,[],[f118,f207,f203])).

fof(f118,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f210,plain,
    ( ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f119,f207,f203])).

fof(f119,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15706)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (15723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (15697)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (15698)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (15706)Refutation not found, incomplete strategy% (15706)------------------------------
% 0.21/0.52  % (15706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15709)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (15703)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (15701)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (15721)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (15720)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (15717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (15724)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (15722)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (15700)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.54  % (15714)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.54  % (15716)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.54  % (15696)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.54  % (15708)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.54  % (15712)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.54  % (15706)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (15706)Memory used [KB]: 11001
% 1.42/0.54  % (15706)Time elapsed: 0.112 s
% 1.42/0.54  % (15706)------------------------------
% 1.42/0.54  % (15706)------------------------------
% 1.42/0.54  % (15702)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.54  % (15704)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.54  % (15713)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.54  % (15707)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (15719)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.55  % (15710)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (15705)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (15718)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  % (15711)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.55  % (15712)Refutation not found, incomplete strategy% (15712)------------------------------
% 1.55/0.55  % (15712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (15716)Refutation not found, incomplete strategy% (15716)------------------------------
% 1.55/0.56  % (15716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (15695)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.55/0.56  % (15705)Refutation not found, incomplete strategy% (15705)------------------------------
% 1.55/0.56  % (15705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (15716)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (15716)Memory used [KB]: 1918
% 1.55/0.56  % (15716)Time elapsed: 0.151 s
% 1.55/0.56  % (15716)------------------------------
% 1.55/0.56  % (15716)------------------------------
% 1.55/0.57  % (15712)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (15712)Memory used [KB]: 10746
% 1.55/0.57  % (15712)Time elapsed: 0.148 s
% 1.55/0.57  % (15712)------------------------------
% 1.55/0.57  % (15712)------------------------------
% 1.55/0.57  % (15704)Refutation not found, incomplete strategy% (15704)------------------------------
% 1.55/0.57  % (15704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (15705)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  % (15717)Refutation not found, incomplete strategy% (15717)------------------------------
% 1.55/0.58  % (15717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  
% 1.55/0.58  % (15705)Memory used [KB]: 10874
% 1.55/0.58  % (15705)Time elapsed: 0.151 s
% 1.55/0.58  % (15705)------------------------------
% 1.55/0.58  % (15705)------------------------------
% 1.55/0.58  % (15717)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (15717)Memory used [KB]: 11129
% 1.55/0.58  % (15717)Time elapsed: 0.136 s
% 1.55/0.58  % (15717)------------------------------
% 1.55/0.58  % (15717)------------------------------
% 1.55/0.58  % (15704)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (15704)Memory used [KB]: 10874
% 1.55/0.58  % (15704)Time elapsed: 0.153 s
% 1.55/0.58  % (15704)------------------------------
% 1.55/0.58  % (15704)------------------------------
% 1.55/0.59  % (15695)Refutation not found, incomplete strategy% (15695)------------------------------
% 1.55/0.59  % (15695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (15695)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (15695)Memory used [KB]: 2046
% 1.55/0.61  % (15695)Time elapsed: 0.189 s
% 1.55/0.61  % (15695)------------------------------
% 1.55/0.61  % (15695)------------------------------
% 2.37/0.68  % (15725)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.37/0.70  % (15727)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.37/0.71  % (15729)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.37/0.71  % (15728)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.37/0.72  % (15730)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.37/0.72  % (15731)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.83/0.76  % (15732)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.95/0.82  % (15700)Time limit reached!
% 2.95/0.82  % (15700)------------------------------
% 2.95/0.82  % (15700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.82  % (15700)Termination reason: Time limit
% 2.95/0.82  
% 2.95/0.82  % (15700)Memory used [KB]: 8955
% 2.95/0.82  % (15700)Time elapsed: 0.413 s
% 2.95/0.82  % (15700)------------------------------
% 2.95/0.82  % (15700)------------------------------
% 3.46/0.92  % (15707)Time limit reached!
% 3.46/0.92  % (15707)------------------------------
% 3.46/0.92  % (15707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.92  % (15707)Termination reason: Time limit
% 3.46/0.92  % (15707)Termination phase: Saturation
% 3.46/0.92  
% 3.46/0.92  % (15707)Memory used [KB]: 8443
% 3.46/0.92  % (15707)Time elapsed: 0.500 s
% 3.46/0.92  % (15707)------------------------------
% 3.46/0.92  % (15707)------------------------------
% 3.46/0.92  % (15696)Time limit reached!
% 3.46/0.92  % (15696)------------------------------
% 3.46/0.92  % (15696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.92  % (15696)Termination reason: Time limit
% 3.46/0.92  
% 3.46/0.92  % (15696)Memory used [KB]: 7291
% 3.46/0.92  % (15696)Time elapsed: 0.514 s
% 3.46/0.92  % (15696)------------------------------
% 3.46/0.92  % (15696)------------------------------
% 4.15/1.00  % (15733)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.15/1.01  % (15730)Time limit reached!
% 4.15/1.01  % (15730)------------------------------
% 4.15/1.01  % (15730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/1.01  % (15730)Termination reason: Time limit
% 4.15/1.01  
% 4.15/1.01  % (15730)Memory used [KB]: 12792
% 4.15/1.01  % (15730)Time elapsed: 0.402 s
% 4.15/1.01  % (15730)------------------------------
% 4.15/1.01  % (15730)------------------------------
% 4.15/1.01  % (15711)Time limit reached!
% 4.15/1.01  % (15711)------------------------------
% 4.15/1.01  % (15711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/1.01  % (15711)Termination reason: Time limit
% 4.15/1.01  % (15711)Termination phase: Saturation
% 4.15/1.01  
% 4.15/1.01  % (15711)Memory used [KB]: 15479
% 4.15/1.01  % (15711)Time elapsed: 0.608 s
% 4.15/1.01  % (15711)------------------------------
% 4.15/1.01  % (15711)------------------------------
% 4.15/1.02  % (15729)Time limit reached!
% 4.15/1.02  % (15729)------------------------------
% 4.15/1.02  % (15729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/1.02  % (15729)Termination reason: Time limit
% 4.15/1.02  
% 4.15/1.02  % (15729)Memory used [KB]: 7036
% 4.15/1.02  % (15729)Time elapsed: 0.414 s
% 4.15/1.02  % (15729)------------------------------
% 4.15/1.02  % (15729)------------------------------
% 4.15/1.03  % (15702)Time limit reached!
% 4.15/1.03  % (15702)------------------------------
% 4.15/1.03  % (15702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.04  % (15723)Time limit reached!
% 4.75/1.04  % (15723)------------------------------
% 4.75/1.04  % (15723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.04  % (15723)Termination reason: Time limit
% 4.75/1.04  
% 4.75/1.04  % (15723)Memory used [KB]: 7291
% 4.75/1.04  % (15723)Time elapsed: 0.635 s
% 4.75/1.04  % (15723)------------------------------
% 4.75/1.04  % (15723)------------------------------
% 4.75/1.05  % (15722)Refutation found. Thanks to Tanya!
% 4.75/1.05  % SZS status Theorem for theBenchmark
% 4.75/1.05  % SZS output start Proof for theBenchmark
% 4.75/1.05  fof(f10990,plain,(
% 4.75/1.05    $false),
% 4.75/1.05    inference(avatar_sat_refutation,[],[f210,f211,f1551,f1649,f1888,f1892,f5786,f5834,f5848,f5855,f7262,f8742,f9535,f9540,f9697,f9739,f9835,f9898,f9901,f10021,f10029,f10071,f10077,f10283,f10363,f10376,f10380,f10467,f10492,f10496,f10826,f10827,f10858,f10917,f10944,f10956,f10981])).
% 4.75/1.05  fof(f10981,plain,(
% 4.75/1.05    ~spl16_6 | ~spl16_9 | spl16_48),
% 4.75/1.05    inference(avatar_split_clause,[],[f8313,f1636,f288,f274])).
% 4.75/1.05  fof(f274,plain,(
% 4.75/1.05    spl16_6 <=> v1_xboole_0(u1_struct_0(sK6))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).
% 4.75/1.05  fof(f288,plain,(
% 4.75/1.05    spl16_9 <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).
% 4.75/1.05  fof(f1636,plain,(
% 4.75/1.05    spl16_48 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).
% 4.75/1.05  fof(f8313,plain,(
% 4.75/1.05    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_xboole_0(u1_struct_0(sK6)) | spl16_48),
% 4.75/1.05    inference(superposition,[],[f1638,f216])).
% 4.75/1.05  fof(f216,plain,(
% 4.75/1.05    ( ! [X0,X1] : (k2_zfmisc_1(X1,X0) = X0 | ~v1_xboole_0(X0)) )),
% 4.75/1.05    inference(superposition,[],[f196,f140])).
% 4.75/1.05  fof(f140,plain,(
% 4.75/1.05    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f35])).
% 4.75/1.05  fof(f35,plain,(
% 4.75/1.05    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.75/1.05    inference(ennf_transformation,[],[f4])).
% 4.75/1.05  fof(f4,axiom,(
% 4.75/1.05    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 4.75/1.05  fof(f196,plain,(
% 4.75/1.05    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.75/1.05    inference(equality_resolution,[],[f177])).
% 4.75/1.05  fof(f177,plain,(
% 4.75/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.75/1.05    inference(cnf_transformation,[],[f104])).
% 4.75/1.05  fof(f104,plain,(
% 4.75/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.75/1.05    inference(flattening,[],[f103])).
% 4.75/1.05  fof(f103,plain,(
% 4.75/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.75/1.05    inference(nnf_transformation,[],[f7])).
% 4.75/1.05  fof(f7,axiom,(
% 4.75/1.05    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 4.75/1.05  fof(f1638,plain,(
% 4.75/1.05    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | spl16_48),
% 4.75/1.05    inference(avatar_component_clause,[],[f1636])).
% 4.75/1.05  fof(f10956,plain,(
% 4.75/1.05    spl16_329 | ~spl16_2),
% 4.75/1.05    inference(avatar_split_clause,[],[f10955,f207,f9756])).
% 4.75/1.05  fof(f9756,plain,(
% 4.75/1.05    spl16_329 <=> v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_329])])).
% 4.75/1.05  fof(f207,plain,(
% 4.75/1.05    spl16_2 <=> v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 4.75/1.05  fof(f10955,plain,(
% 4.75/1.05    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_2),
% 4.75/1.05    inference(forward_demodulation,[],[f208,f117])).
% 4.75/1.05  fof(f117,plain,(
% 4.75/1.05    sK7 = sK8),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f71,plain,(
% 4.75/1.05    ((((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = sK8 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 4.75/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f66,f70,f69,f68,f67])).
% 4.75/1.05  fof(f67,plain,(
% 4.75/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK5,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK5,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 4.75/1.05    introduced(choice_axiom,[])).
% 4.75/1.05  fof(f68,plain,(
% 4.75/1.05    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK5,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK5,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(X2,sK5,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(X2,sK5,sK6)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 4.75/1.05    introduced(choice_axiom,[])).
% 4.75/1.05  fof(f69,plain,(
% 4.75/1.05    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(X2,sK5,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(X2,sK5,sK6)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7))),
% 4.75/1.05    introduced(choice_axiom,[])).
% 4.75/1.05  fof(f70,plain,(
% 4.75/1.05    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = sK8 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(sK8))),
% 4.75/1.05    introduced(choice_axiom,[])).
% 4.75/1.05  fof(f66,plain,(
% 4.75/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.75/1.05    inference(flattening,[],[f65])).
% 4.75/1.05  fof(f65,plain,(
% 4.75/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.75/1.05    inference(nnf_transformation,[],[f31])).
% 4.75/1.05  fof(f31,plain,(
% 4.75/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.75/1.05    inference(flattening,[],[f30])).
% 4.75/1.05  fof(f30,plain,(
% 4.75/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.75/1.05    inference(ennf_transformation,[],[f28])).
% 4.75/1.05  fof(f28,negated_conjecture,(
% 4.75/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.75/1.05    inference(negated_conjecture,[],[f27])).
% 4.75/1.05  fof(f27,conjecture,(
% 4.75/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 4.75/1.05  fof(f208,plain,(
% 4.75/1.05    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_2),
% 4.75/1.05    inference(avatar_component_clause,[],[f207])).
% 4.75/1.05  fof(f10944,plain,(
% 4.75/1.05    spl16_4 | ~spl16_33),
% 4.75/1.05    inference(avatar_split_clause,[],[f5954,f722,f243])).
% 4.75/1.05  fof(f243,plain,(
% 4.75/1.05    spl16_4 <=> v1_xboole_0(sK7)),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 4.75/1.05  fof(f722,plain,(
% 4.75/1.05    spl16_33 <=> ! [X11] : ~r2_hidden(X11,sK7)),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_33])])).
% 4.75/1.05  fof(f5954,plain,(
% 4.75/1.05    v1_xboole_0(sK7) | ~spl16_33),
% 4.75/1.05    inference(resolution,[],[f723,f148])).
% 4.75/1.05  fof(f148,plain,(
% 4.75/1.05    ( ! [X0] : (r2_hidden(sK12(X0),X0) | v1_xboole_0(X0)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f89])).
% 4.75/1.05  fof(f89,plain,(
% 4.75/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK12(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.75/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f87,f88])).
% 4.75/1.05  fof(f88,plain,(
% 4.75/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK12(X0),X0))),
% 4.75/1.05    introduced(choice_axiom,[])).
% 4.75/1.05  fof(f87,plain,(
% 4.75/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.75/1.05    inference(rectify,[],[f86])).
% 4.75/1.05  fof(f86,plain,(
% 4.75/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.75/1.05    inference(nnf_transformation,[],[f1])).
% 4.75/1.05  fof(f1,axiom,(
% 4.75/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 4.75/1.05  fof(f723,plain,(
% 4.75/1.05    ( ! [X11] : (~r2_hidden(X11,sK7)) ) | ~spl16_33),
% 4.75/1.05    inference(avatar_component_clause,[],[f722])).
% 4.75/1.05  fof(f10917,plain,(
% 4.75/1.05    spl16_124 | ~spl16_139),
% 4.75/1.05    inference(avatar_split_clause,[],[f8228,f5784,f5529])).
% 4.75/1.05  fof(f5529,plain,(
% 4.75/1.05    spl16_124 <=> ! [X4] : (~v4_relat_1(sK7,X4) | ~v1_xboole_0(X4))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_124])])).
% 4.75/1.05  fof(f5784,plain,(
% 4.75/1.05    spl16_139 <=> ! [X4] : (~v4_relat_1(sK7,X4) | r2_hidden(sK12(u1_struct_0(sK5)),X4))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_139])])).
% 4.75/1.05  fof(f8228,plain,(
% 4.75/1.05    ( ! [X1] : (~v4_relat_1(sK7,X1) | ~v1_xboole_0(X1)) ) | ~spl16_139),
% 4.75/1.05    inference(resolution,[],[f5785,f147])).
% 4.75/1.05  fof(f147,plain,(
% 4.75/1.05    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f89])).
% 4.75/1.05  fof(f5785,plain,(
% 4.75/1.05    ( ! [X4] : (r2_hidden(sK12(u1_struct_0(sK5)),X4) | ~v4_relat_1(sK7,X4)) ) | ~spl16_139),
% 4.75/1.05    inference(avatar_component_clause,[],[f5784])).
% 4.75/1.05  fof(f10858,plain,(
% 4.75/1.05    spl16_6 | spl16_113),
% 4.75/1.05    inference(avatar_split_clause,[],[f10857,f5306,f274])).
% 4.75/1.05  fof(f5306,plain,(
% 4.75/1.05    spl16_113 <=> v1_partfun1(sK7,u1_struct_0(sK5))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_113])])).
% 4.75/1.05  fof(f10857,plain,(
% 4.75/1.05    v1_partfun1(sK7,u1_struct_0(sK5)) | v1_xboole_0(u1_struct_0(sK6))),
% 4.75/1.05    inference(subsumption_resolution,[],[f10856,f111])).
% 4.75/1.05  fof(f111,plain,(
% 4.75/1.05    v1_funct_1(sK7)),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f10856,plain,(
% 4.75/1.05    ~v1_funct_1(sK7) | v1_partfun1(sK7,u1_struct_0(sK5)) | v1_xboole_0(u1_struct_0(sK6))),
% 4.75/1.05    inference(subsumption_resolution,[],[f6408,f112])).
% 4.75/1.05  fof(f112,plain,(
% 4.75/1.05    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f6408,plain,(
% 4.75/1.05    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(sK7) | v1_partfun1(sK7,u1_struct_0(sK5)) | v1_xboole_0(u1_struct_0(sK6))),
% 4.75/1.05    inference(resolution,[],[f113,f155])).
% 4.75/1.05  fof(f155,plain,(
% 4.75/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f44])).
% 4.75/1.05  fof(f44,plain,(
% 4.75/1.05    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.75/1.05    inference(flattening,[],[f43])).
% 4.75/1.05  fof(f43,plain,(
% 4.75/1.05    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.75/1.05    inference(ennf_transformation,[],[f17])).
% 4.75/1.05  fof(f17,axiom,(
% 4.75/1.05    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 4.75/1.05  fof(f113,plain,(
% 4.75/1.05    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f10827,plain,(
% 4.75/1.05    ~spl16_47 | spl16_1 | ~spl16_49 | ~spl16_48),
% 4.75/1.05    inference(avatar_split_clause,[],[f10360,f1636,f1640,f203,f1632])).
% 4.75/1.05  fof(f1632,plain,(
% 4.75/1.05    spl16_47 <=> v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_47])])).
% 4.75/1.05  fof(f203,plain,(
% 4.75/1.05    spl16_1 <=> v5_pre_topc(sK7,sK5,sK6)),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 4.75/1.05  fof(f1640,plain,(
% 4.75/1.05    spl16_49 <=> v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_49])])).
% 4.75/1.05  fof(f10360,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10359,f107])).
% 4.75/1.05  fof(f107,plain,(
% 4.75/1.05    v2_pre_topc(sK5)),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f10359,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10358,f108])).
% 4.75/1.05  fof(f108,plain,(
% 4.75/1.05    l1_pre_topc(sK5)),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f10358,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10357,f109])).
% 4.75/1.05  fof(f109,plain,(
% 4.75/1.05    v2_pre_topc(sK6)),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f10357,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10356,f110])).
% 4.75/1.05  fof(f110,plain,(
% 4.75/1.05    l1_pre_topc(sK6)),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f10356,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10355,f112])).
% 4.75/1.05  fof(f10355,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10354,f113])).
% 4.75/1.05  fof(f10354,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10183,f111])).
% 4.75/1.05  fof(f10183,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(resolution,[],[f1637,f199])).
% 4.75/1.05  fof(f199,plain,(
% 4.75/1.05    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.05    inference(duplicate_literal_removal,[],[f191])).
% 4.75/1.05  fof(f191,plain,(
% 4.75/1.05    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.05    inference(equality_resolution,[],[f146])).
% 4.75/1.05  fof(f146,plain,(
% 4.75/1.05    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f85])).
% 4.75/1.05  fof(f85,plain,(
% 4.75/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.75/1.05    inference(nnf_transformation,[],[f41])).
% 4.75/1.05  fof(f41,plain,(
% 4.75/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.75/1.05    inference(flattening,[],[f40])).
% 4.75/1.05  fof(f40,plain,(
% 4.75/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.75/1.05    inference(ennf_transformation,[],[f25])).
% 4.75/1.05  fof(f25,axiom,(
% 4.75/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 4.75/1.05  fof(f1637,plain,(
% 4.75/1.05    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~spl16_48),
% 4.75/1.05    inference(avatar_component_clause,[],[f1636])).
% 4.75/1.05  fof(f10826,plain,(
% 4.75/1.05    ~spl16_47 | spl16_49 | ~spl16_1 | ~spl16_48),
% 4.75/1.05    inference(avatar_split_clause,[],[f10370,f1636,f203,f1640,f1632])).
% 4.75/1.05  fof(f10370,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10369,f107])).
% 4.75/1.05  fof(f10369,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10368,f108])).
% 4.75/1.05  fof(f10368,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10367,f109])).
% 4.75/1.05  fof(f10367,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10366,f110])).
% 4.75/1.05  fof(f10366,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10365,f112])).
% 4.75/1.05  fof(f10365,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10364,f113])).
% 4.75/1.05  fof(f10364,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(subsumption_resolution,[],[f10184,f111])).
% 4.75/1.05  fof(f10184,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_48),
% 4.75/1.05    inference(resolution,[],[f1637,f198])).
% 4.75/1.05  fof(f198,plain,(
% 4.75/1.05    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.05    inference(duplicate_literal_removal,[],[f192])).
% 4.75/1.05  fof(f192,plain,(
% 4.75/1.05    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.05    inference(equality_resolution,[],[f145])).
% 4.75/1.05  fof(f145,plain,(
% 4.75/1.05    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f85])).
% 4.75/1.05  fof(f10496,plain,(
% 4.75/1.05    ~spl16_6 | spl16_9),
% 4.75/1.05    inference(avatar_split_clause,[],[f6422,f288,f274])).
% 4.75/1.05  fof(f6422,plain,(
% 4.75/1.05    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_xboole_0(u1_struct_0(sK6))),
% 4.75/1.05    inference(superposition,[],[f113,f216])).
% 4.75/1.05  fof(f10492,plain,(
% 4.75/1.05    ~spl16_6 | spl16_149),
% 4.75/1.05    inference(avatar_split_clause,[],[f7393,f5867,f274])).
% 4.75/1.05  fof(f5867,plain,(
% 4.75/1.05    spl16_149 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_149])])).
% 4.75/1.05  fof(f7393,plain,(
% 4.75/1.05    ~v1_xboole_0(u1_struct_0(sK6)) | spl16_149),
% 4.75/1.05    inference(duplicate_literal_removal,[],[f7392])).
% 4.75/1.05  fof(f7392,plain,(
% 4.75/1.05    ~v1_xboole_0(u1_struct_0(sK6)) | ~v1_xboole_0(u1_struct_0(sK6)) | spl16_149),
% 4.75/1.05    inference(superposition,[],[f5869,f216])).
% 4.75/1.05  fof(f5869,plain,(
% 4.75/1.05    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) | spl16_149),
% 4.75/1.05    inference(avatar_component_clause,[],[f5867])).
% 4.75/1.05  fof(f10467,plain,(
% 4.75/1.05    ~spl16_6 | spl16_33),
% 4.75/1.05    inference(avatar_split_clause,[],[f10466,f722,f274])).
% 4.75/1.05  fof(f10466,plain,(
% 4.75/1.05    ( ! [X1] : (~r2_hidden(X1,sK7) | ~v1_xboole_0(u1_struct_0(sK6))) )),
% 4.75/1.05    inference(subsumption_resolution,[],[f8812,f147])).
% 4.75/1.05  fof(f8812,plain,(
% 4.75/1.05    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK6)) | ~r2_hidden(X1,sK7) | ~v1_xboole_0(u1_struct_0(sK6))) )),
% 4.75/1.05    inference(superposition,[],[f630,f216])).
% 4.75/1.05  fof(f630,plain,(
% 4.75/1.05    ( ! [X10] : (r2_hidden(X10,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) | ~r2_hidden(X10,sK7)) )),
% 4.75/1.05    inference(resolution,[],[f170,f254])).
% 4.75/1.05  fof(f254,plain,(
% 4.75/1.05    r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))),
% 4.75/1.05    inference(resolution,[],[f173,f113])).
% 4.75/1.05  fof(f173,plain,(
% 4.75/1.05    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f102])).
% 4.75/1.05  fof(f102,plain,(
% 4.75/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.75/1.05    inference(nnf_transformation,[],[f11])).
% 4.75/1.05  fof(f11,axiom,(
% 4.75/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 4.75/1.05  fof(f170,plain,(
% 4.75/1.05    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f101])).
% 4.75/1.05  fof(f101,plain,(
% 4.75/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK14(X0,X1),X1) & r2_hidden(sK14(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.75/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f99,f100])).
% 4.75/1.05  fof(f100,plain,(
% 4.75/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK14(X0,X1),X1) & r2_hidden(sK14(X0,X1),X0)))),
% 4.75/1.05    introduced(choice_axiom,[])).
% 4.75/1.05  fof(f99,plain,(
% 4.75/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.75/1.05    inference(rectify,[],[f98])).
% 4.75/1.05  fof(f98,plain,(
% 4.75/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.75/1.05    inference(nnf_transformation,[],[f52])).
% 4.75/1.05  fof(f52,plain,(
% 4.75/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.75/1.05    inference(ennf_transformation,[],[f2])).
% 4.75/1.05  fof(f2,axiom,(
% 4.75/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 4.75/1.05  fof(f10380,plain,(
% 4.75/1.05    ~spl16_4 | spl16_13),
% 4.75/1.05    inference(avatar_split_clause,[],[f10097,f307,f243])).
% 4.75/1.05  fof(f307,plain,(
% 4.75/1.05    spl16_13 <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).
% 4.75/1.05  fof(f10097,plain,(
% 4.75/1.05    ~v1_xboole_0(sK7) | spl16_13),
% 4.75/1.05    inference(resolution,[],[f308,f214])).
% 4.75/1.05  fof(f214,plain,(
% 4.75/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 4.75/1.05    inference(superposition,[],[f121,f140])).
% 4.75/1.05  fof(f121,plain,(
% 4.75/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.75/1.05    inference(cnf_transformation,[],[f10])).
% 4.75/1.05  fof(f10,axiom,(
% 4.75/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 4.75/1.05  fof(f308,plain,(
% 4.75/1.05    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) | spl16_13),
% 4.75/1.05    inference(avatar_component_clause,[],[f307])).
% 4.75/1.05  fof(f10376,plain,(
% 4.75/1.05    ~spl16_329 | spl16_2),
% 4.75/1.05    inference(avatar_split_clause,[],[f10375,f207,f9756])).
% 4.75/1.05  fof(f10375,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | spl16_2),
% 4.75/1.05    inference(forward_demodulation,[],[f209,f117])).
% 4.75/1.05  fof(f209,plain,(
% 4.75/1.05    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | spl16_2),
% 4.75/1.05    inference(avatar_component_clause,[],[f207])).
% 4.75/1.05  fof(f10363,plain,(
% 4.75/1.05    spl16_1 | ~spl16_49 | ~spl16_48 | ~spl16_113 | ~spl16_233),
% 4.75/1.05    inference(avatar_split_clause,[],[f10362,f7266,f5306,f1636,f1640,f203])).
% 4.75/1.05  fof(f7266,plain,(
% 4.75/1.05    spl16_233 <=> v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_233])])).
% 4.75/1.05  fof(f10362,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | (~spl16_48 | ~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10361,f112])).
% 4.75/1.05  fof(f10361,plain,(
% 4.75/1.05    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6) | (~spl16_48 | ~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(forward_demodulation,[],[f10360,f10180])).
% 4.75/1.05  fof(f10180,plain,(
% 4.75/1.05    u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | (~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10179,f669])).
% 4.75/1.05  fof(f669,plain,(
% 4.75/1.05    v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 4.75/1.05    inference(resolution,[],[f185,f225])).
% 4.75/1.05  fof(f225,plain,(
% 4.75/1.05    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))),
% 4.75/1.05    inference(forward_demodulation,[],[f116,f117])).
% 4.75/1.05  fof(f116,plain,(
% 4.75/1.05    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))),
% 4.75/1.05    inference(cnf_transformation,[],[f71])).
% 4.75/1.05  fof(f185,plain,(
% 4.75/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f54])).
% 4.75/1.05  fof(f54,plain,(
% 4.75/1.05    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.75/1.05    inference(ennf_transformation,[],[f16])).
% 4.75/1.05  fof(f16,axiom,(
% 4.75/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 4.75/1.05  fof(f10179,plain,(
% 4.75/1.05    u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | (~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10176,f668])).
% 4.75/1.05  fof(f668,plain,(
% 4.75/1.05    v4_relat_1(sK7,u1_struct_0(sK5))),
% 4.75/1.05    inference(resolution,[],[f185,f113])).
% 4.75/1.05  fof(f10176,plain,(
% 4.75/1.05    ~v4_relat_1(sK7,u1_struct_0(sK5)) | u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | (~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(resolution,[],[f7875,f7851])).
% 4.75/1.05  fof(f7851,plain,(
% 4.75/1.05    ( ! [X7] : (~r1_tarski(X7,u1_struct_0(sK5)) | u1_struct_0(sK5) = X7 | ~v4_relat_1(sK7,X7)) ) | ~spl16_113),
% 4.75/1.05    inference(resolution,[],[f6083,f169])).
% 4.75/1.05  fof(f169,plain,(
% 4.75/1.05    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f97])).
% 4.75/1.05  fof(f97,plain,(
% 4.75/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.75/1.05    inference(flattening,[],[f96])).
% 4.75/1.05  fof(f96,plain,(
% 4.75/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.75/1.05    inference(nnf_transformation,[],[f5])).
% 4.75/1.05  fof(f5,axiom,(
% 4.75/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.75/1.05  fof(f6083,plain,(
% 4.75/1.05    ( ! [X0] : (r1_tarski(u1_struct_0(sK5),X0) | ~v4_relat_1(sK7,X0)) ) | ~spl16_113),
% 4.75/1.05    inference(subsumption_resolution,[],[f6082,f668])).
% 4.75/1.05  fof(f6082,plain,(
% 4.75/1.05    ( ! [X0] : (~v4_relat_1(sK7,X0) | r1_tarski(u1_struct_0(sK5),X0) | ~v4_relat_1(sK7,u1_struct_0(sK5))) ) | ~spl16_113),
% 4.75/1.05    inference(subsumption_resolution,[],[f6078,f407])).
% 4.75/1.05  fof(f407,plain,(
% 4.75/1.05    v1_relat_1(sK7)),
% 4.75/1.05    inference(resolution,[],[f184,f113])).
% 4.75/1.05  fof(f184,plain,(
% 4.75/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f53])).
% 4.75/1.05  fof(f53,plain,(
% 4.75/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.75/1.05    inference(ennf_transformation,[],[f15])).
% 4.75/1.05  fof(f15,axiom,(
% 4.75/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 4.75/1.05  fof(f6078,plain,(
% 4.75/1.05    ( ! [X0] : (~v4_relat_1(sK7,X0) | ~v1_relat_1(sK7) | r1_tarski(u1_struct_0(sK5),X0) | ~v4_relat_1(sK7,u1_struct_0(sK5))) ) | ~spl16_113),
% 4.75/1.05    inference(resolution,[],[f5307,f1104])).
% 4.75/1.05  fof(f1104,plain,(
% 4.75/1.05    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | r1_tarski(X1,X2) | ~v4_relat_1(X0,X1)) )),
% 4.75/1.05    inference(duplicate_literal_removal,[],[f1094])).
% 4.75/1.05  fof(f1094,plain,(
% 4.75/1.05    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 4.75/1.05    inference(superposition,[],[f156,f165])).
% 4.75/1.05  fof(f165,plain,(
% 4.75/1.05    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f95])).
% 4.75/1.05  fof(f95,plain,(
% 4.75/1.05    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.75/1.05    inference(nnf_transformation,[],[f51])).
% 4.75/1.05  fof(f51,plain,(
% 4.75/1.05    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.75/1.05    inference(flattening,[],[f50])).
% 4.75/1.05  fof(f50,plain,(
% 4.75/1.05    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.75/1.05    inference(ennf_transformation,[],[f18])).
% 4.75/1.05  fof(f18,axiom,(
% 4.75/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 4.75/1.05  fof(f156,plain,(
% 4.75/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.75/1.05    inference(cnf_transformation,[],[f93])).
% 4.75/1.05  fof(f93,plain,(
% 4.75/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.75/1.05    inference(nnf_transformation,[],[f45])).
% 4.75/1.05  fof(f45,plain,(
% 4.75/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.75/1.05    inference(ennf_transformation,[],[f14])).
% 4.75/1.05  fof(f14,axiom,(
% 4.75/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 4.75/1.05  fof(f5307,plain,(
% 4.75/1.05    v1_partfun1(sK7,u1_struct_0(sK5)) | ~spl16_113),
% 4.75/1.05    inference(avatar_component_clause,[],[f5306])).
% 4.75/1.05  fof(f7875,plain,(
% 4.75/1.05    ( ! [X0] : (r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0) | ~v4_relat_1(sK7,X0)) ) | ~spl16_233),
% 4.75/1.05    inference(subsumption_resolution,[],[f7874,f669])).
% 4.75/1.05  fof(f7874,plain,(
% 4.75/1.05    ( ! [X0] : (~v4_relat_1(sK7,X0) | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) ) | ~spl16_233),
% 4.75/1.05    inference(subsumption_resolution,[],[f7870,f407])).
% 4.75/1.05  fof(f7870,plain,(
% 4.75/1.05    ( ! [X0] : (~v4_relat_1(sK7,X0) | ~v1_relat_1(sK7) | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) ) | ~spl16_233),
% 4.75/1.05    inference(resolution,[],[f7268,f1104])).
% 4.75/1.05  fof(f7268,plain,(
% 4.75/1.05    v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~spl16_233),
% 4.75/1.05    inference(avatar_component_clause,[],[f7266])).
% 4.75/1.05  fof(f10283,plain,(
% 4.75/1.05    spl16_47 | ~spl16_113 | ~spl16_233),
% 4.75/1.05    inference(avatar_contradiction_clause,[],[f10282])).
% 4.75/1.05  fof(f10282,plain,(
% 4.75/1.05    $false | (spl16_47 | ~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10218,f112])).
% 4.75/1.05  fof(f10218,plain,(
% 4.75/1.05    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | (spl16_47 | ~spl16_113 | ~spl16_233)),
% 4.75/1.05    inference(backward_demodulation,[],[f1634,f10180])).
% 4.75/1.05  fof(f1634,plain,(
% 4.75/1.05    ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | spl16_47),
% 4.75/1.05    inference(avatar_component_clause,[],[f1632])).
% 4.75/1.05  fof(f10077,plain,(
% 4.75/1.05    ~spl16_42 | ~spl16_325 | spl16_329 | ~spl16_44 | ~spl16_40 | ~spl16_41 | ~spl16_43),
% 4.75/1.05    inference(avatar_split_clause,[],[f10076,f1538,f1530,f1526,f1542,f9756,f9701,f1534])).
% 4.75/1.05  fof(f1534,plain,(
% 4.75/1.05    spl16_42 <=> v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).
% 4.75/1.05  fof(f9701,plain,(
% 4.75/1.05    spl16_325 <=> v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_325])])).
% 4.75/1.05  fof(f1542,plain,(
% 4.75/1.05    spl16_44 <=> v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).
% 4.75/1.05  fof(f1526,plain,(
% 4.75/1.05    spl16_40 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).
% 4.75/1.05  fof(f1530,plain,(
% 4.75/1.05    spl16_41 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).
% 4.75/1.05  % (15702)Termination reason: Time limit
% 4.75/1.05  
% 4.75/1.05  fof(f1538,plain,(
% 4.75/1.05    spl16_43 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))),
% 4.75/1.05    introduced(avatar_definition,[new_symbols(naming,[spl16_43])])).
% 4.75/1.05  % (15702)Memory used [KB]: 10618
% 4.75/1.05  % (15702)Time elapsed: 0.622 s
% 4.75/1.05  % (15702)------------------------------
% 4.75/1.05  % (15702)------------------------------
% 4.75/1.05  fof(f10076,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | (~spl16_40 | ~spl16_41 | ~spl16_43)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10075,f107])).
% 4.75/1.05  fof(f10075,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(sK5) | (~spl16_40 | ~spl16_41 | ~spl16_43)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10074,f108])).
% 4.75/1.05  fof(f10074,plain,(
% 4.75/1.05    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | (~spl16_40 | ~spl16_41 | ~spl16_43)),
% 4.75/1.05    inference(subsumption_resolution,[],[f10073,f1527])).
% 4.75/1.05  fof(f1527,plain,(
% 4.75/1.05    v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_40),
% 4.75/1.05    inference(avatar_component_clause,[],[f1526])).
% 4.75/1.05  % (15735)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.75/1.06  fof(f10073,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | (~spl16_41 | ~spl16_43)),
% 4.75/1.06    inference(subsumption_resolution,[],[f10072,f1531])).
% 4.75/1.06  fof(f1531,plain,(
% 4.75/1.06    l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_41),
% 4.75/1.06    inference(avatar_component_clause,[],[f1530])).
% 4.75/1.06  fof(f10072,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f9766,f1539])).
% 4.75/1.06  fof(f1539,plain,(
% 4.75/1.06    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) | ~spl16_43),
% 4.75/1.06    inference(avatar_component_clause,[],[f1538])).
% 4.75/1.06  fof(f9766,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.75/1.06    inference(subsumption_resolution,[],[f7231,f111])).
% 4.75/1.06  fof(f7231,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.75/1.06    inference(resolution,[],[f225,f198])).
% 4.75/1.06  fof(f10071,plain,(
% 4.75/1.06    ~spl16_42 | ~spl16_325 | spl16_44 | ~spl16_329 | ~spl16_40 | ~spl16_41 | ~spl16_43),
% 4.75/1.06    inference(avatar_split_clause,[],[f10070,f1538,f1530,f1526,f9756,f1542,f9701,f1534])).
% 4.75/1.06  fof(f10070,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | (~spl16_40 | ~spl16_41 | ~spl16_43)),
% 4.75/1.06    inference(subsumption_resolution,[],[f10069,f107])).
% 4.75/1.06  fof(f10069,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(sK5) | (~spl16_40 | ~spl16_41 | ~spl16_43)),
% 4.75/1.06    inference(subsumption_resolution,[],[f10068,f108])).
% 4.75/1.06  fof(f10068,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | (~spl16_40 | ~spl16_41 | ~spl16_43)),
% 4.75/1.06    inference(subsumption_resolution,[],[f10067,f1527])).
% 4.75/1.06  fof(f10067,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | (~spl16_41 | ~spl16_43)),
% 4.75/1.06    inference(subsumption_resolution,[],[f10066,f1531])).
% 4.75/1.06  fof(f10066,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f9773,f1539])).
% 4.75/1.06  fof(f9773,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.75/1.06    inference(subsumption_resolution,[],[f7230,f111])).
% 4.75/1.06  fof(f7230,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.75/1.06    inference(resolution,[],[f225,f199])).
% 4.75/1.06  fof(f10029,plain,(
% 4.75/1.06    ~spl16_42 | spl16_44 | ~spl16_1 | ~spl16_43),
% 4.75/1.06    inference(avatar_split_clause,[],[f10028,f1538,f203,f1542,f1534])).
% 4.75/1.06  fof(f10028,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10027,f107])).
% 4.75/1.06  fof(f10027,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10026,f108])).
% 4.75/1.06  fof(f10026,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10025,f109])).
% 4.75/1.06  fof(f10025,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10024,f110])).
% 4.75/1.06  fof(f10024,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10023,f112])).
% 4.75/1.06  fof(f10023,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10022,f113])).
% 4.75/1.06  fof(f10022,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f9957,f111])).
% 4.75/1.06  fof(f9957,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,sK6) | v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(resolution,[],[f1539,f200])).
% 4.75/1.06  fof(f200,plain,(
% 4.75/1.06    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.06    inference(duplicate_literal_removal,[],[f190])).
% 4.75/1.06  fof(f190,plain,(
% 4.75/1.06    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.06    inference(equality_resolution,[],[f143])).
% 4.75/1.06  fof(f143,plain,(
% 4.75/1.06    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.06    inference(cnf_transformation,[],[f84])).
% 4.75/1.06  fof(f84,plain,(
% 4.75/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.75/1.06    inference(nnf_transformation,[],[f39])).
% 4.75/1.06  fof(f39,plain,(
% 4.75/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.75/1.06    inference(flattening,[],[f38])).
% 4.75/1.06  fof(f38,plain,(
% 4.75/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.75/1.06    inference(ennf_transformation,[],[f26])).
% 4.75/1.06  fof(f26,axiom,(
% 4.75/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.75/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 4.75/1.06  fof(f10021,plain,(
% 4.75/1.06    ~spl16_42 | spl16_1 | ~spl16_44 | ~spl16_43),
% 4.75/1.06    inference(avatar_split_clause,[],[f10020,f1538,f1542,f203,f1534])).
% 4.75/1.06  fof(f10020,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10019,f107])).
% 4.75/1.06  fof(f10019,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10018,f108])).
% 4.75/1.06  fof(f10018,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10017,f109])).
% 4.75/1.06  fof(f10017,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10016,f110])).
% 4.75/1.06  fof(f10016,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10015,f112])).
% 4.75/1.06  fof(f10015,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f10014,f113])).
% 4.75/1.06  fof(f10014,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(subsumption_resolution,[],[f9956,f111])).
% 4.75/1.06  fof(f9956,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~spl16_43),
% 4.75/1.06    inference(resolution,[],[f1539,f201])).
% 4.75/1.06  fof(f201,plain,(
% 4.75/1.06    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.06    inference(duplicate_literal_removal,[],[f189])).
% 4.75/1.06  fof(f189,plain,(
% 4.75/1.06    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.06    inference(equality_resolution,[],[f144])).
% 4.75/1.06  fof(f144,plain,(
% 4.75/1.06    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.06    inference(cnf_transformation,[],[f84])).
% 4.75/1.06  fof(f9901,plain,(
% 4.75/1.06    spl16_233 | ~spl16_325 | spl16_10),
% 4.75/1.06    inference(avatar_split_clause,[],[f9900,f293,f9701,f7266])).
% 4.75/1.06  fof(f293,plain,(
% 4.75/1.06    spl16_10 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).
% 4.75/1.06  fof(f9900,plain,(
% 4.75/1.06    ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | spl16_10),
% 4.75/1.06    inference(subsumption_resolution,[],[f9899,f295])).
% 4.75/1.06  fof(f295,plain,(
% 4.75/1.06    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | spl16_10),
% 4.75/1.06    inference(avatar_component_clause,[],[f293])).
% 4.75/1.06  fof(f9899,plain,(
% 4.75/1.06    ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(subsumption_resolution,[],[f9858,f111])).
% 4.75/1.06  fof(f9858,plain,(
% 4.75/1.06    ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(resolution,[],[f225,f155])).
% 4.75/1.06  fof(f9898,plain,(
% 4.75/1.06    ~spl16_47 | ~spl16_48 | ~spl16_325 | spl16_329 | ~spl16_49 | ~spl16_45 | ~spl16_46),
% 4.75/1.06    inference(avatar_split_clause,[],[f9897,f1628,f1624,f1640,f9756,f9701,f1636,f1632])).
% 4.75/1.06  fof(f1624,plain,(
% 4.75/1.06    spl16_45 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).
% 4.75/1.06  fof(f1628,plain,(
% 4.75/1.06    spl16_46 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    introduced(avatar_definition,[new_symbols(naming,[spl16_46])])).
% 4.75/1.06  fof(f9897,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | (~spl16_45 | ~spl16_46)),
% 4.75/1.06    inference(subsumption_resolution,[],[f9896,f1625])).
% 4.75/1.06  fof(f1625,plain,(
% 4.75/1.06    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_45),
% 4.75/1.06    inference(avatar_component_clause,[],[f1624])).
% 4.75/1.06  fof(f9896,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_46),
% 4.75/1.06    inference(subsumption_resolution,[],[f9895,f1629])).
% 4.75/1.06  fof(f1629,plain,(
% 4.75/1.06    l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_46),
% 4.75/1.06    inference(avatar_component_clause,[],[f1628])).
% 4.75/1.06  fof(f9895,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    inference(subsumption_resolution,[],[f9894,f109])).
% 4.75/1.06  fof(f9894,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    inference(subsumption_resolution,[],[f9893,f110])).
% 4.75/1.06  fof(f9893,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    inference(subsumption_resolution,[],[f9857,f111])).
% 4.75/1.06  fof(f9857,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    inference(resolution,[],[f225,f200])).
% 4.75/1.06  fof(f9835,plain,(
% 4.75/1.06    spl16_325),
% 4.75/1.06    inference(avatar_split_clause,[],[f219,f9701])).
% 4.75/1.06  fof(f219,plain,(
% 4.75/1.06    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(forward_demodulation,[],[f115,f117])).
% 4.75/1.06  fof(f115,plain,(
% 4.75/1.06    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(cnf_transformation,[],[f71])).
% 4.75/1.06  fof(f9739,plain,(
% 4.75/1.06    ~spl16_10 | ~spl16_124),
% 4.75/1.06    inference(avatar_split_clause,[],[f9738,f5529,f293])).
% 4.75/1.06  fof(f9738,plain,(
% 4.75/1.06    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~spl16_124),
% 4.75/1.06    inference(subsumption_resolution,[],[f1455,f5626])).
% 4.75/1.06  fof(f5626,plain,(
% 4.75/1.06    ( ! [X4] : (~r1_tarski(sK7,X4) | ~v1_xboole_0(X4)) ) | ~spl16_124),
% 4.75/1.06    inference(duplicate_literal_removal,[],[f5620])).
% 4.75/1.06  fof(f5620,plain,(
% 4.75/1.06    ( ! [X4] : (~v1_xboole_0(X4) | ~r1_tarski(sK7,X4) | ~v1_xboole_0(X4)) ) | ~spl16_124),
% 4.75/1.06    inference(resolution,[],[f5530,f1907])).
% 4.75/1.06  fof(f1907,plain,(
% 4.75/1.06    ( ! [X4,X2] : (v4_relat_1(X4,X2) | ~r1_tarski(X4,X2) | ~v1_xboole_0(X2)) )),
% 4.75/1.06    inference(superposition,[],[f665,f217])).
% 4.75/1.06  fof(f217,plain,(
% 4.75/1.06    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 4.75/1.06    inference(superposition,[],[f197,f140])).
% 4.75/1.06  fof(f197,plain,(
% 4.75/1.06    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.75/1.06    inference(equality_resolution,[],[f176])).
% 4.75/1.06  fof(f176,plain,(
% 4.75/1.06    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.75/1.06    inference(cnf_transformation,[],[f104])).
% 4.75/1.06  fof(f665,plain,(
% 4.75/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 4.75/1.06    inference(resolution,[],[f185,f174])).
% 4.75/1.06  fof(f174,plain,(
% 4.75/1.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.75/1.06    inference(cnf_transformation,[],[f102])).
% 4.75/1.06  fof(f5530,plain,(
% 4.75/1.06    ( ! [X4] : (~v4_relat_1(sK7,X4) | ~v1_xboole_0(X4)) ) | ~spl16_124),
% 4.75/1.06    inference(avatar_component_clause,[],[f5529])).
% 4.75/1.06  fof(f1455,plain,(
% 4.75/1.06    r1_tarski(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(superposition,[],[f255,f216])).
% 4.75/1.06  fof(f255,plain,(
% 4.75/1.06    r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))),
% 4.75/1.06    inference(resolution,[],[f173,f225])).
% 4.75/1.06  fof(f9697,plain,(
% 4.75/1.06    ~spl16_10 | ~spl16_13 | spl16_43),
% 4.75/1.06    inference(avatar_split_clause,[],[f8280,f1538,f307,f293])).
% 4.75/1.06  fof(f8280,plain,(
% 4.75/1.06    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | spl16_43),
% 4.75/1.06    inference(superposition,[],[f1540,f216])).
% 4.75/1.06  fof(f1540,plain,(
% 4.75/1.06    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) | spl16_43),
% 4.75/1.06    inference(avatar_component_clause,[],[f1538])).
% 4.75/1.06  fof(f9540,plain,(
% 4.75/1.06    spl16_10 | spl16_48 | ~spl16_113),
% 4.75/1.06    inference(avatar_contradiction_clause,[],[f9539])).
% 4.75/1.06  fof(f9539,plain,(
% 4.75/1.06    $false | (spl16_10 | spl16_48 | ~spl16_113)),
% 4.75/1.06    inference(subsumption_resolution,[],[f9476,f254])).
% 4.75/1.06  fof(f9476,plain,(
% 4.75/1.06    ~r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) | (spl16_10 | spl16_48 | ~spl16_113)),
% 4.75/1.06    inference(backward_demodulation,[],[f8308,f9427])).
% 4.75/1.06  fof(f9427,plain,(
% 4.75/1.06    u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | (spl16_10 | ~spl16_113)),
% 4.75/1.06    inference(subsumption_resolution,[],[f9426,f668])).
% 4.75/1.06  fof(f9426,plain,(
% 4.75/1.06    u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v4_relat_1(sK7,u1_struct_0(sK5)) | (spl16_10 | ~spl16_113)),
% 4.75/1.06    inference(subsumption_resolution,[],[f9401,f669])).
% 4.75/1.06  fof(f9401,plain,(
% 4.75/1.06    u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v4_relat_1(sK7,u1_struct_0(sK5)) | (spl16_10 | ~spl16_113)),
% 4.75/1.06    inference(resolution,[],[f7851,f5127])).
% 4.75/1.06  fof(f5127,plain,(
% 4.75/1.06    ( ! [X16] : (r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X16) | ~v4_relat_1(sK7,X16)) ) | spl16_10),
% 4.75/1.06    inference(subsumption_resolution,[],[f5126,f669])).
% 4.75/1.06  fof(f5126,plain,(
% 4.75/1.06    ( ! [X16] : (~v4_relat_1(sK7,X16) | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X16) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) ) | spl16_10),
% 4.75/1.06    inference(subsumption_resolution,[],[f5120,f407])).
% 4.75/1.06  fof(f5120,plain,(
% 4.75/1.06    ( ! [X16] : (~v4_relat_1(sK7,X16) | ~v1_relat_1(sK7) | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X16) | ~v4_relat_1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) ) | spl16_10),
% 4.75/1.06    inference(resolution,[],[f1104,f1160])).
% 4.75/1.06  fof(f1160,plain,(
% 4.75/1.06    v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | spl16_10),
% 4.75/1.06    inference(subsumption_resolution,[],[f1159,f295])).
% 4.75/1.06  fof(f1159,plain,(
% 4.75/1.06    v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(subsumption_resolution,[],[f1158,f111])).
% 4.75/1.06  fof(f1158,plain,(
% 4.75/1.06    ~v1_funct_1(sK7) | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(subsumption_resolution,[],[f1142,f219])).
% 4.75/1.06  fof(f1142,plain,(
% 4.75/1.06    ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | v1_partfun1(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 4.75/1.06    inference(resolution,[],[f155,f225])).
% 4.75/1.06  fof(f8308,plain,(
% 4.75/1.06    ~r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) | spl16_48),
% 4.75/1.06    inference(resolution,[],[f1638,f174])).
% 4.75/1.06  fof(f9535,plain,(
% 4.75/1.06    spl16_10 | spl16_43 | ~spl16_113),
% 4.75/1.06    inference(avatar_contradiction_clause,[],[f9534])).
% 4.75/1.06  fof(f9534,plain,(
% 4.75/1.06    $false | (spl16_10 | spl16_43 | ~spl16_113)),
% 4.75/1.06    inference(subsumption_resolution,[],[f9458,f8275])).
% 4.75/1.06  fof(f8275,plain,(
% 4.75/1.06    ~r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) | spl16_43),
% 4.75/1.06    inference(resolution,[],[f1540,f174])).
% 4.75/1.06  fof(f9458,plain,(
% 4.75/1.06    r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) | (spl16_10 | ~spl16_113)),
% 4.75/1.06    inference(backward_demodulation,[],[f255,f9427])).
% 4.75/1.06  fof(f8742,plain,(
% 4.75/1.06    ~spl16_149 | ~spl16_124),
% 4.75/1.06    inference(avatar_split_clause,[],[f8731,f5529,f5867])).
% 4.75/1.06  fof(f8731,plain,(
% 4.75/1.06    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) | ~spl16_124),
% 4.75/1.06    inference(resolution,[],[f254,f5626])).
% 4.75/1.06  fof(f7262,plain,(
% 4.75/1.06    ~spl16_45 | ~spl16_46 | ~spl16_47 | ~spl16_48 | spl16_49 | ~spl16_2),
% 4.75/1.06    inference(avatar_split_clause,[],[f7261,f207,f1640,f1636,f1632,f1628,f1624])).
% 4.75/1.06  fof(f7261,plain,(
% 4.75/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_2),
% 4.75/1.06    inference(subsumption_resolution,[],[f7260,f109])).
% 4.75/1.06  fof(f7260,plain,(
% 4.75/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_2),
% 4.75/1.06    inference(subsumption_resolution,[],[f7259,f110])).
% 4.75/1.06  fof(f7259,plain,(
% 4.75/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_2),
% 4.75/1.06    inference(subsumption_resolution,[],[f7258,f111])).
% 4.75/1.06  fof(f7258,plain,(
% 4.75/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_2),
% 4.75/1.06    inference(subsumption_resolution,[],[f7257,f219])).
% 4.75/1.06  fof(f7257,plain,(
% 4.75/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~spl16_2),
% 4.75/1.06    inference(subsumption_resolution,[],[f7232,f218])).
% 4.75/1.06  fof(f218,plain,(
% 4.75/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~spl16_2),
% 4.75/1.06    inference(forward_demodulation,[],[f208,f117])).
% 4.75/1.06  fof(f7232,plain,(
% 4.75/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) | ~v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 4.75/1.06    inference(resolution,[],[f225,f201])).
% 4.75/1.06  fof(f5855,plain,(
% 4.75/1.06    ~spl16_4 | ~spl16_6 | spl16_47),
% 4.75/1.06    inference(avatar_split_clause,[],[f2546,f1632,f274,f243])).
% 4.75/1.06  fof(f2546,plain,(
% 4.75/1.06    ~v1_xboole_0(u1_struct_0(sK6)) | ~v1_xboole_0(sK7) | spl16_47),
% 4.75/1.06    inference(resolution,[],[f1087,f1634])).
% 4.75/1.06  fof(f1087,plain,(
% 4.75/1.06    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 4.75/1.06    inference(superposition,[],[f1063,f140])).
% 4.75/1.06  fof(f1063,plain,(
% 4.75/1.06    ( ! [X10,X11] : (v1_funct_2(k1_xboole_0,X10,X11) | ~v1_xboole_0(X11)) )),
% 4.75/1.06    inference(superposition,[],[f183,f1011])).
% 4.75/1.06  fof(f1011,plain,(
% 4.75/1.06    ( ! [X0,X1] : (k1_xboole_0 = sK15(X1,X0) | ~v1_xboole_0(X0)) )),
% 4.75/1.06    inference(resolution,[],[f926,f564])).
% 4.75/1.06  fof(f564,plain,(
% 4.75/1.06    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 4.75/1.06    inference(resolution,[],[f169,f256])).
% 4.75/1.06  fof(f256,plain,(
% 4.75/1.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.75/1.06    inference(resolution,[],[f173,f121])).
% 4.75/1.06  fof(f926,plain,(
% 4.75/1.06    ( ! [X6,X4,X5] : (r1_tarski(sK15(X5,X4),X6) | ~v1_xboole_0(X4)) )),
% 4.75/1.06    inference(resolution,[],[f641,f171])).
% 4.75/1.06  fof(f171,plain,(
% 4.75/1.06    ( ! [X0,X1] : (r2_hidden(sK14(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 4.75/1.06    inference(cnf_transformation,[],[f101])).
% 4.75/1.06  fof(f641,plain,(
% 4.75/1.06    ( ! [X24,X23,X25] : (~r2_hidden(X23,sK15(X24,X25)) | ~v1_xboole_0(X25)) )),
% 4.75/1.06    inference(subsumption_resolution,[],[f637,f147])).
% 4.75/1.06  fof(f637,plain,(
% 4.75/1.06    ( ! [X24,X23,X25] : (~r2_hidden(X23,sK15(X24,X25)) | r2_hidden(X23,X25) | ~v1_xboole_0(X25)) )),
% 4.75/1.06    inference(resolution,[],[f170,f496])).
% 4.75/1.06  fof(f496,plain,(
% 4.75/1.06    ( ! [X4,X3] : (r1_tarski(sK15(X3,X4),X4) | ~v1_xboole_0(X4)) )),
% 4.75/1.06    inference(superposition,[],[f397,f216])).
% 4.75/1.06  fof(f397,plain,(
% 4.75/1.06    ( ! [X0,X1] : (r1_tarski(sK15(X0,X1),k2_zfmisc_1(X0,X1))) )),
% 4.75/1.06    inference(resolution,[],[f178,f173])).
% 4.75/1.06  fof(f178,plain,(
% 4.75/1.06    ( ! [X0,X1] : (m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.75/1.06    inference(cnf_transformation,[],[f106])).
% 4.75/1.06  fof(f106,plain,(
% 4.75/1.06    ! [X0,X1] : (v1_funct_2(sK15(X0,X1),X0,X1) & v1_funct_1(sK15(X0,X1)) & v5_relat_1(sK15(X0,X1),X1) & v4_relat_1(sK15(X0,X1),X0) & v1_relat_1(sK15(X0,X1)) & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.75/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f19,f105])).
% 4.75/1.06  fof(f105,plain,(
% 4.75/1.06    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK15(X0,X1),X0,X1) & v1_funct_1(sK15(X0,X1)) & v5_relat_1(sK15(X0,X1),X1) & v4_relat_1(sK15(X0,X1),X0) & v1_relat_1(sK15(X0,X1)) & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.75/1.06    introduced(choice_axiom,[])).
% 4.75/1.06  fof(f19,axiom,(
% 4.75/1.06    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.75/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 4.75/1.06  fof(f183,plain,(
% 4.75/1.06    ( ! [X0,X1] : (v1_funct_2(sK15(X0,X1),X0,X1)) )),
% 4.75/1.06    inference(cnf_transformation,[],[f106])).
% 4.75/1.06  fof(f5848,plain,(
% 4.75/1.06    ~spl16_4 | ~spl16_14 | spl16_42),
% 4.75/1.06    inference(avatar_split_clause,[],[f2542,f1534,f325,f243])).
% 4.75/1.06  fof(f325,plain,(
% 4.75/1.06    spl16_14 <=> v1_xboole_0(u1_struct_0(sK5))),
% 4.75/1.06    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).
% 4.75/1.06  fof(f2542,plain,(
% 4.75/1.06    ~v1_xboole_0(u1_struct_0(sK5)) | ~v1_xboole_0(sK7) | spl16_42),
% 4.75/1.06    inference(resolution,[],[f1055,f1536])).
% 4.75/1.06  fof(f1536,plain,(
% 4.75/1.06    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) | spl16_42),
% 4.75/1.06    inference(avatar_component_clause,[],[f1534])).
% 4.75/1.06  fof(f1055,plain,(
% 4.75/1.06    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 4.75/1.06    inference(superposition,[],[f1031,f140])).
% 4.75/1.07  fof(f1031,plain,(
% 4.75/1.07    ( ! [X10,X11] : (v1_funct_2(k1_xboole_0,X10,X11) | ~v1_xboole_0(X10)) )),
% 4.75/1.07    inference(superposition,[],[f183,f998])).
% 4.75/1.07  fof(f998,plain,(
% 4.75/1.07    ( ! [X0,X1] : (k1_xboole_0 = sK15(X0,X1) | ~v1_xboole_0(X0)) )),
% 4.75/1.07    inference(resolution,[],[f910,f564])).
% 4.75/1.07  fof(f910,plain,(
% 4.75/1.07    ( ! [X6,X4,X5] : (r1_tarski(sK15(X4,X5),X6) | ~v1_xboole_0(X4)) )),
% 4.75/1.07    inference(resolution,[],[f640,f171])).
% 4.75/1.07  fof(f640,plain,(
% 4.75/1.07    ( ! [X21,X22,X20] : (~r2_hidden(X20,sK15(X21,X22)) | ~v1_xboole_0(X21)) )),
% 4.75/1.07    inference(subsumption_resolution,[],[f636,f147])).
% 4.75/1.07  fof(f636,plain,(
% 4.75/1.07    ( ! [X21,X22,X20] : (~r2_hidden(X20,sK15(X21,X22)) | r2_hidden(X20,X21) | ~v1_xboole_0(X21)) )),
% 4.75/1.07    inference(resolution,[],[f170,f495])).
% 4.75/1.07  fof(f495,plain,(
% 4.75/1.07    ( ! [X2,X1] : (r1_tarski(sK15(X1,X2),X1) | ~v1_xboole_0(X1)) )),
% 4.75/1.07    inference(superposition,[],[f397,f217])).
% 4.75/1.07  fof(f5834,plain,(
% 4.75/1.07    ~spl16_14 | spl16_33),
% 4.75/1.07    inference(avatar_split_clause,[],[f5833,f722,f325])).
% 4.75/1.07  fof(f5833,plain,(
% 4.75/1.07    ( ! [X0] : (~r2_hidden(X0,sK7) | ~v1_xboole_0(u1_struct_0(sK5))) )),
% 4.75/1.07    inference(subsumption_resolution,[],[f644,f147])).
% 4.75/1.07  fof(f644,plain,(
% 4.75/1.07    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK5)) | ~r2_hidden(X0,sK7) | ~v1_xboole_0(u1_struct_0(sK5))) )),
% 4.75/1.07    inference(superposition,[],[f630,f217])).
% 4.75/1.07  fof(f5786,plain,(
% 4.75/1.07    spl16_14 | spl16_139 | ~spl16_113),
% 4.75/1.07    inference(avatar_split_clause,[],[f5715,f5306,f5784,f325])).
% 4.75/1.07  fof(f5715,plain,(
% 4.75/1.07    ( ! [X4] : (~v4_relat_1(sK7,X4) | r2_hidden(sK12(u1_struct_0(sK5)),X4) | v1_xboole_0(u1_struct_0(sK5))) ) | ~spl16_113),
% 4.75/1.07    inference(resolution,[],[f5484,f148])).
% 4.75/1.07  fof(f5484,plain,(
% 4.75/1.07    ( ! [X6,X5] : (~r2_hidden(X6,u1_struct_0(sK5)) | ~v4_relat_1(sK7,X5) | r2_hidden(X6,X5)) ) | ~spl16_113),
% 4.75/1.07    inference(resolution,[],[f5386,f170])).
% 4.75/1.07  fof(f5386,plain,(
% 4.75/1.07    ( ! [X0] : (r1_tarski(u1_struct_0(sK5),X0) | ~v4_relat_1(sK7,X0)) ) | ~spl16_113),
% 4.75/1.07    inference(subsumption_resolution,[],[f5385,f668])).
% 4.75/1.07  fof(f5385,plain,(
% 4.75/1.07    ( ! [X0] : (~v4_relat_1(sK7,X0) | r1_tarski(u1_struct_0(sK5),X0) | ~v4_relat_1(sK7,u1_struct_0(sK5))) ) | ~spl16_113),
% 4.75/1.07    inference(subsumption_resolution,[],[f5381,f407])).
% 4.75/1.07  fof(f5381,plain,(
% 4.75/1.07    ( ! [X0] : (~v4_relat_1(sK7,X0) | ~v1_relat_1(sK7) | r1_tarski(u1_struct_0(sK5),X0) | ~v4_relat_1(sK7,u1_struct_0(sK5))) ) | ~spl16_113),
% 4.75/1.07    inference(resolution,[],[f5307,f1104])).
% 4.75/1.07  fof(f1892,plain,(
% 4.75/1.07    spl16_46),
% 4.75/1.07    inference(avatar_contradiction_clause,[],[f1891])).
% 4.75/1.07  fof(f1891,plain,(
% 4.75/1.07    $false | spl16_46),
% 4.75/1.07    inference(subsumption_resolution,[],[f1889,f108])).
% 4.75/1.07  fof(f1889,plain,(
% 4.75/1.07    ~l1_pre_topc(sK5) | spl16_46),
% 4.75/1.07    inference(resolution,[],[f1884,f443])).
% 4.75/1.07  fof(f443,plain,(
% 4.75/1.07    ( ! [X0] : (r1_tarski(u1_pre_topc(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.75/1.07    inference(resolution,[],[f122,f173])).
% 4.75/1.07  fof(f122,plain,(
% 4.75/1.07    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 4.75/1.07    inference(cnf_transformation,[],[f32])).
% 4.75/1.07  fof(f32,plain,(
% 4.75/1.07    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.75/1.07    inference(ennf_transformation,[],[f23])).
% 4.75/1.07  fof(f23,axiom,(
% 4.75/1.07    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.75/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 4.75/1.07  fof(f1884,plain,(
% 4.75/1.07    ~r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) | spl16_46),
% 4.75/1.07    inference(resolution,[],[f533,f1630])).
% 4.75/1.07  fof(f1630,plain,(
% 4.75/1.07    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | spl16_46),
% 4.75/1.07    inference(avatar_component_clause,[],[f1628])).
% 4.75/1.07  fof(f533,plain,(
% 4.75/1.07    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~r1_tarski(X1,k1_zfmisc_1(X0))) )),
% 4.75/1.07    inference(resolution,[],[f160,f174])).
% 4.75/1.07  fof(f160,plain,(
% 4.75/1.07    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 4.75/1.07    inference(cnf_transformation,[],[f47])).
% 4.75/1.07  fof(f47,plain,(
% 4.75/1.07    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.75/1.07    inference(ennf_transformation,[],[f22])).
% 4.75/1.07  fof(f22,axiom,(
% 4.75/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 4.75/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 4.75/1.07  fof(f1888,plain,(
% 4.75/1.07    spl16_41),
% 4.75/1.07    inference(avatar_contradiction_clause,[],[f1887])).
% 4.75/1.07  fof(f1887,plain,(
% 4.75/1.07    $false | spl16_41),
% 4.75/1.07    inference(subsumption_resolution,[],[f1885,f110])).
% 4.75/1.07  fof(f1885,plain,(
% 4.75/1.07    ~l1_pre_topc(sK6) | spl16_41),
% 4.75/1.07    inference(resolution,[],[f1883,f443])).
% 4.75/1.07  fof(f1883,plain,(
% 4.75/1.07    ~r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) | spl16_41),
% 4.75/1.07    inference(resolution,[],[f533,f1532])).
% 4.75/1.07  fof(f1532,plain,(
% 4.75/1.07    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | spl16_41),
% 4.75/1.07    inference(avatar_component_clause,[],[f1530])).
% 4.75/1.07  fof(f1649,plain,(
% 4.75/1.07    spl16_45),
% 4.75/1.07    inference(avatar_contradiction_clause,[],[f1648])).
% 4.75/1.07  fof(f1648,plain,(
% 4.75/1.07    $false | spl16_45),
% 4.75/1.07    inference(subsumption_resolution,[],[f1647,f107])).
% 4.75/1.07  fof(f1647,plain,(
% 4.75/1.07    ~v2_pre_topc(sK5) | spl16_45),
% 4.75/1.07    inference(subsumption_resolution,[],[f1646,f108])).
% 4.75/1.07  fof(f1646,plain,(
% 4.75/1.07    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | spl16_45),
% 4.75/1.07    inference(resolution,[],[f1626,f142])).
% 4.75/1.07  fof(f142,plain,(
% 4.75/1.07    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.75/1.07    inference(cnf_transformation,[],[f37])).
% 4.75/1.07  fof(f37,plain,(
% 4.75/1.07    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.75/1.07    inference(flattening,[],[f36])).
% 4.75/1.07  fof(f36,plain,(
% 4.75/1.07    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.75/1.07    inference(ennf_transformation,[],[f24])).
% 4.75/1.07  fof(f24,axiom,(
% 4.75/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 4.75/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 4.75/1.07  fof(f1626,plain,(
% 4.75/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | spl16_45),
% 4.75/1.07    inference(avatar_component_clause,[],[f1624])).
% 4.75/1.07  fof(f1551,plain,(
% 4.75/1.07    spl16_40),
% 4.75/1.07    inference(avatar_contradiction_clause,[],[f1550])).
% 4.75/1.07  fof(f1550,plain,(
% 4.75/1.07    $false | spl16_40),
% 4.75/1.07    inference(subsumption_resolution,[],[f1549,f109])).
% 4.75/1.07  fof(f1549,plain,(
% 4.75/1.07    ~v2_pre_topc(sK6) | spl16_40),
% 4.75/1.07    inference(subsumption_resolution,[],[f1548,f110])).
% 4.75/1.07  fof(f1548,plain,(
% 4.75/1.07    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | spl16_40),
% 4.75/1.07    inference(resolution,[],[f1528,f142])).
% 4.75/1.07  fof(f1528,plain,(
% 4.75/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | spl16_40),
% 4.75/1.07    inference(avatar_component_clause,[],[f1526])).
% 4.75/1.07  fof(f211,plain,(
% 4.75/1.07    spl16_1 | spl16_2),
% 4.75/1.07    inference(avatar_split_clause,[],[f118,f207,f203])).
% 4.75/1.07  fof(f118,plain,(
% 4.75/1.07    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)),
% 4.75/1.07    inference(cnf_transformation,[],[f71])).
% 4.75/1.07  fof(f210,plain,(
% 4.75/1.07    ~spl16_1 | ~spl16_2),
% 4.75/1.07    inference(avatar_split_clause,[],[f119,f207,f203])).
% 4.75/1.07  fof(f119,plain,(
% 4.75/1.07    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)),
% 4.75/1.07    inference(cnf_transformation,[],[f71])).
% 4.75/1.07  % SZS output end Proof for theBenchmark
% 4.75/1.07  % (15722)------------------------------
% 4.75/1.07  % (15722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.07  % (15722)Termination reason: Refutation
% 4.75/1.07  
% 4.75/1.07  % (15722)Memory used [KB]: 10234
% 4.75/1.07  % (15722)Time elapsed: 0.626 s
% 4.75/1.07  % (15722)------------------------------
% 4.75/1.07  % (15722)------------------------------
% 4.75/1.07  % (15694)Success in time 0.709 s
%------------------------------------------------------------------------------
