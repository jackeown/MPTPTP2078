%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 386 expanded)
%              Number of leaves         :   47 ( 198 expanded)
%              Depth                    :   10
%              Number of atoms          :  721 (2086 expanded)
%              Number of equality atoms :  119 ( 286 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f106,f110,f114,f118,f165,f187,f191,f201,f208,f230,f238,f244,f260,f267,f278,f282,f291,f294,f301,f321,f327,f333,f334])).

fof(f334,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f333,plain,
    ( spl6_44
    | ~ spl6_3
    | ~ spl6_33
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f329,f324,f265,f84,f331])).

fof(f331,plain,
    ( spl6_44
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f84,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f265,plain,
    ( spl6_33
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f324,plain,
    ( spl6_43
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f329,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_3
    | ~ spl6_33
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f328,f266])).

fof(f266,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f265])).

fof(f328,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_3
    | ~ spl6_43 ),
    inference(resolution,[],[f325,f85])).

fof(f85,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f324])).

fof(f327,plain,
    ( spl6_43
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f322,f319,f96,f108,f104,f100,f324])).

fof(f100,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f104,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f108,plain,
    ( spl6_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f96,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f319,plain,
    ( spl6_42
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X1,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f322,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(resolution,[],[f320,f97])).

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f320,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X1,sK0)
        | ~ m1_subset_1(X0,X1)
        | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0)) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f319])).

fof(f321,plain,
    ( spl6_10
    | ~ spl6_2
    | spl6_42
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f317,f92,f88,f319,f80,f112])).

fof(f112,plain,
    ( spl6_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f80,plain,
    ( spl6_2
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f88,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f92,plain,
    ( spl6_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f317,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ v1_partfun1(sK4,sK0)
        | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | ~ v1_funct_2(X2,X1,sK0)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f261,f89])).

fof(f89,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f261,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X1,X2)
        | ~ v1_partfun1(sK4,X0)
        | k3_funct_2(X2,X3,k8_funct_2(X2,X0,X3,X4,sK4),X1) = k1_funct_1(sK4,k3_funct_2(X2,X0,X4,X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X4,X2,X0)
        | ~ v1_funct_1(X4)
        | v1_xboole_0(X2)
        | v1_xboole_0(X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f54,f93])).

fof(f93,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(f301,plain,
    ( spl6_39
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f297,f289,f280,f269,f299])).

fof(f299,plain,
    ( spl6_39
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f269,plain,
    ( spl6_34
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f280,plain,
    ( spl6_36
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f289,plain,
    ( spl6_38
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f297,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f296,f270])).

fof(f270,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f296,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_36
    | ~ spl6_38 ),
    inference(resolution,[],[f290,f281])).

fof(f281,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f280])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f289])).

fof(f294,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f293,f286,f88,f80,f112])).

fof(f286,plain,
    ( spl6_37
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f293,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_4
    | ~ spl6_37 ),
    inference(resolution,[],[f292,f89])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
        | ~ v1_partfun1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl6_37 ),
    inference(resolution,[],[f287,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f287,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f286])).

fof(f291,plain,
    ( spl6_10
    | spl6_37
    | ~ spl6_19
    | spl6_38
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f284,f92,f88,f289,f173,f286,f112])).

fof(f173,plain,
    ( spl6_19
  <=> v1_funct_2(sK4,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f217,f89])).

fof(f217,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,X1)
        | ~ v1_funct_2(sK4,X1,X2)
        | k3_funct_2(X1,X2,sK4,X0) = k7_partfun1(X2,sK4,X0)
        | v1_xboole_0(X2)
        | v1_xboole_0(X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f53,f93])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f282,plain,
    ( ~ spl6_3
    | spl6_36
    | ~ spl6_23
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f273,f265,f199,f280,f84])).

fof(f199,plain,
    ( spl6_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f273,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_23
    | ~ spl6_33 ),
    inference(superposition,[],[f200,f266])).

fof(f200,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f278,plain,
    ( spl6_34
    | ~ spl6_29
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f272,f265,f242,f269])).

fof(f242,plain,
    ( spl6_29
  <=> k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f272,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_29
    | ~ spl6_33 ),
    inference(superposition,[],[f243,f266])).

fof(f243,plain,
    ( k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f267,plain,
    ( spl6_33
    | ~ spl6_3
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f263,f258,f84,f265])).

fof(f258,plain,
    ( spl6_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f263,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_3
    | ~ spl6_32 ),
    inference(resolution,[],[f259,f85])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl6_9
    | ~ spl6_7
    | spl6_32
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f256,f104,f96,f258,f100,f108])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
        | v1_xboole_0(sK1) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f203,f97])).

fof(f203,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X3,X4)
        | ~ v1_funct_2(sK3,X4,X5)
        | k3_funct_2(X4,X5,sK3,X3) = k1_funct_1(sK3,X3)
        | v1_xboole_0(X4) )
    | ~ spl6_8 ),
    inference(resolution,[],[f68,f105])).

fof(f105,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f244,plain,
    ( spl6_29
    | ~ spl6_3
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f240,f206,f199,f84,f242])).

fof(f206,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f240,plain,
    ( k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_3
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(resolution,[],[f239,f85])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(resolution,[],[f207,f200])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f238,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f233,f228,f116,f80,f112])).

fof(f116,plain,
    ( spl6_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f228,plain,
    ( spl6_28
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f233,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_11
    | ~ spl6_28 ),
    inference(resolution,[],[f229,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ v1_partfun1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f55,f117])).

fof(f117,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f229,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl6_28
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f222,f182,f88,f228])).

fof(f182,plain,
    ( spl6_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f222,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(superposition,[],[f89,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f208,plain,
    ( spl6_10
    | ~ spl6_19
    | spl6_24
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f204,f92,f88,f206,f173,f112])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
        | v1_xboole_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f202,f89])).

fof(f202,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,X1)
        | ~ v1_funct_2(sK4,X1,X2)
        | k3_funct_2(X1,X2,sK4,X0) = k1_funct_1(sK4,X0)
        | v1_xboole_0(X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f68,f93])).

fof(f201,plain,
    ( spl6_9
    | ~ spl6_7
    | spl6_23
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f195,f104,f96,f199,f100,f108])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f168,f97])).

fof(f168,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X3,X4)
        | ~ v1_funct_2(sK3,X4,X5)
        | m1_subset_1(k3_funct_2(X4,X5,sK3,X3),X5)
        | v1_xboole_0(X4) )
    | ~ spl6_8 ),
    inference(resolution,[],[f67,f105])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f191,plain,
    ( ~ spl6_4
    | ~ spl6_18
    | spl6_22 ),
    inference(avatar_split_clause,[],[f190,f185,f162,f88])).

fof(f162,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f185,plain,
    ( spl6_22
  <=> sK0 = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f190,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_18
    | spl6_22 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_18
    | spl6_22 ),
    inference(forward_demodulation,[],[f188,f163])).

fof(f163,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f188,plain,
    ( sK0 != k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_22 ),
    inference(superposition,[],[f186,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f186,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK4)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( ~ spl6_4
    | spl6_21
    | ~ spl6_22
    | spl6_19 ),
    inference(avatar_split_clause,[],[f179,f173,f185,f182,f88])).

fof(f179,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_19 ),
    inference(resolution,[],[f174,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f174,plain,
    ( ~ v1_funct_2(sK4,sK0,sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f165,plain,
    ( spl6_18
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f160,f88,f80,f162])).

fof(f160,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ spl6_4 ),
    inference(resolution,[],[f157,f89])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK4,X0)
        | k1_relat_1(sK4) = X0 )
    | ~ spl6_4 ),
    inference(resolution,[],[f121,f89])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f119,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f56,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f118,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f114,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f42,f112])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f38,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                    & v1_partfun1(X4,sK0)
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
            & v1_funct_2(X3,X1,sK0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                  & v1_partfun1(X4,sK0)
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                & v1_partfun1(X4,sK0)
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
              & v1_partfun1(X4,sK0)
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
            & v1_partfun1(X4,sK0)
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
          & v1_partfun1(sK4,sK0)
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X5] :
        ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
        & v1_partfun1(sK4,sK0)
        & m1_subset_1(X5,sK1) )
   => ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
      & v1_partfun1(sK4,sK0)
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f110,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f44,f104])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f102,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f46,f96])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f47,f92])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f49,f84])).

fof(f49,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f50,f80])).

fof(f50,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f51,f76])).

fof(f76,plain,
    ( spl6_1
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f51,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:55:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (1580)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.43  % (1578)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.44  % (1588)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.45  % (1580)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f335,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f106,f110,f114,f118,f165,f187,f191,f201,f208,f230,f238,f244,f260,f267,f278,f282,f291,f294,f301,f321,f327,f333,f334])).
% 0.22/0.45  fof(f334,plain,(
% 0.22/0.45    k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5) | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.45  fof(f333,plain,(
% 0.22/0.45    spl6_44 | ~spl6_3 | ~spl6_33 | ~spl6_43),
% 0.22/0.45    inference(avatar_split_clause,[],[f329,f324,f265,f84,f331])).
% 0.22/0.45  fof(f331,plain,(
% 0.22/0.45    spl6_44 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl6_3 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.45  fof(f265,plain,(
% 0.22/0.45    spl6_33 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.45  fof(f324,plain,(
% 0.22/0.45    spl6_43 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.22/0.45  fof(f329,plain,(
% 0.22/0.45    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_3 | ~spl6_33 | ~spl6_43)),
% 0.22/0.45    inference(forward_demodulation,[],[f328,f266])).
% 0.22/0.45  fof(f266,plain,(
% 0.22/0.45    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~spl6_33),
% 0.22/0.45    inference(avatar_component_clause,[],[f265])).
% 0.22/0.45  fof(f328,plain,(
% 0.22/0.45    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_3 | ~spl6_43)),
% 0.22/0.45    inference(resolution,[],[f325,f85])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    m1_subset_1(sK5,sK1) | ~spl6_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f84])).
% 0.22/0.45  fof(f325,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | ~spl6_43),
% 0.22/0.45    inference(avatar_component_clause,[],[f324])).
% 0.22/0.45  fof(f327,plain,(
% 0.22/0.45    spl6_43 | ~spl6_7 | ~spl6_8 | spl6_9 | ~spl6_6 | ~spl6_42),
% 0.22/0.45    inference(avatar_split_clause,[],[f322,f319,f96,f108,f104,f100,f324])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    spl6_8 <=> v1_funct_1(sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    spl6_9 <=> v1_xboole_0(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.45  fof(f319,plain,(
% 0.22/0.45    spl6_42 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X1,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.45  fof(f322,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_6 | ~spl6_42)),
% 0.22/0.45    inference(resolution,[],[f320,f97])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f96])).
% 0.22/0.45  fof(f320,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X1,sK0) | ~m1_subset_1(X0,X1) | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0))) ) | ~spl6_42),
% 0.22/0.45    inference(avatar_component_clause,[],[f319])).
% 0.22/0.45  fof(f321,plain,(
% 0.22/0.45    spl6_10 | ~spl6_2 | spl6_42 | ~spl6_4 | ~spl6_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f317,f92,f88,f319,f80,f112])).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    spl6_10 <=> v1_xboole_0(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    spl6_2 <=> v1_partfun1(sK4,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    spl6_5 <=> v1_funct_1(sK4)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.45  fof(f317,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~v1_funct_2(X2,X1,sK0) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.22/0.45    inference(resolution,[],[f261,f89])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f88])).
% 0.22/0.45  fof(f261,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X1,X2) | ~v1_partfun1(sK4,X0) | k3_funct_2(X2,X3,k8_funct_2(X2,X0,X3,X4,sK4),X1) = k1_funct_1(sK4,k3_funct_2(X2,X0,X4,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X4,X2,X0) | ~v1_funct_1(X4) | v1_xboole_0(X2) | v1_xboole_0(X0)) ) | ~spl6_5),
% 0.22/0.45    inference(resolution,[],[f54,f93])).
% 0.22/0.45  fof(f93,plain,(
% 0.22/0.45    v1_funct_1(sK4) | ~spl6_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f92])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.22/0.45  fof(f301,plain,(
% 0.22/0.45    spl6_39 | ~spl6_34 | ~spl6_36 | ~spl6_38),
% 0.22/0.45    inference(avatar_split_clause,[],[f297,f289,f280,f269,f299])).
% 0.22/0.45  fof(f299,plain,(
% 0.22/0.45    spl6_39 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.45  fof(f269,plain,(
% 0.22/0.45    spl6_34 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.45  fof(f280,plain,(
% 0.22/0.45    spl6_36 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.45  fof(f289,plain,(
% 0.22/0.45    spl6_38 <=> ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.45  fof(f297,plain,(
% 0.22/0.45    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_34 | ~spl6_36 | ~spl6_38)),
% 0.22/0.45    inference(forward_demodulation,[],[f296,f270])).
% 0.22/0.45  fof(f270,plain,(
% 0.22/0.45    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_34),
% 0.22/0.45    inference(avatar_component_clause,[],[f269])).
% 0.22/0.45  fof(f296,plain,(
% 0.22/0.45    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_36 | ~spl6_38)),
% 0.22/0.45    inference(resolution,[],[f290,f281])).
% 0.22/0.45  fof(f281,plain,(
% 0.22/0.45    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_36),
% 0.22/0.45    inference(avatar_component_clause,[],[f280])).
% 0.22/0.45  fof(f290,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | ~spl6_38),
% 0.22/0.45    inference(avatar_component_clause,[],[f289])).
% 0.22/0.45  fof(f294,plain,(
% 0.22/0.45    spl6_10 | ~spl6_2 | ~spl6_4 | ~spl6_37),
% 0.22/0.45    inference(avatar_split_clause,[],[f293,f286,f88,f80,f112])).
% 0.22/0.45  fof(f286,plain,(
% 0.22/0.45    spl6_37 <=> v1_xboole_0(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.45  fof(f293,plain,(
% 0.22/0.45    ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0) | (~spl6_4 | ~spl6_37)),
% 0.22/0.45    inference(resolution,[],[f292,f89])).
% 0.22/0.45  fof(f292,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1)) ) | ~spl6_37),
% 0.22/0.45    inference(resolution,[],[f287,f55])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.22/0.45  fof(f287,plain,(
% 0.22/0.45    v1_xboole_0(sK2) | ~spl6_37),
% 0.22/0.45    inference(avatar_component_clause,[],[f286])).
% 0.22/0.45  fof(f291,plain,(
% 0.22/0.45    spl6_10 | spl6_37 | ~spl6_19 | spl6_38 | ~spl6_4 | ~spl6_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f284,f92,f88,f289,f173,f286,f112])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    spl6_19 <=> v1_funct_2(sK4,sK0,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.45  fof(f284,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | ~v1_funct_2(sK4,sK0,sK2) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.22/0.45    inference(resolution,[],[f217,f89])).
% 0.22/0.45  fof(f217,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK4,X1,X2) | k3_funct_2(X1,X2,sK4,X0) = k7_partfun1(X2,sK4,X0) | v1_xboole_0(X2) | v1_xboole_0(X1)) ) | ~spl6_5),
% 0.22/0.45    inference(resolution,[],[f53,f93])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.22/0.45  fof(f282,plain,(
% 0.22/0.45    ~spl6_3 | spl6_36 | ~spl6_23 | ~spl6_33),
% 0.22/0.45    inference(avatar_split_clause,[],[f273,f265,f199,f280,f84])).
% 0.22/0.45  fof(f199,plain,(
% 0.22/0.45    spl6_23 <=> ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.45  fof(f273,plain,(
% 0.22/0.45    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~m1_subset_1(sK5,sK1) | (~spl6_23 | ~spl6_33)),
% 0.22/0.45    inference(superposition,[],[f200,f266])).
% 0.22/0.45  fof(f200,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | ~spl6_23),
% 0.22/0.45    inference(avatar_component_clause,[],[f199])).
% 0.22/0.45  fof(f278,plain,(
% 0.22/0.45    spl6_34 | ~spl6_29 | ~spl6_33),
% 0.22/0.45    inference(avatar_split_clause,[],[f272,f265,f242,f269])).
% 0.22/0.45  fof(f242,plain,(
% 0.22/0.45    spl6_29 <=> k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.45  fof(f272,plain,(
% 0.22/0.45    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_29 | ~spl6_33)),
% 0.22/0.45    inference(superposition,[],[f243,f266])).
% 0.22/0.45  fof(f243,plain,(
% 0.22/0.45    k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~spl6_29),
% 0.22/0.45    inference(avatar_component_clause,[],[f242])).
% 0.22/0.45  fof(f267,plain,(
% 0.22/0.45    spl6_33 | ~spl6_3 | ~spl6_32),
% 0.22/0.45    inference(avatar_split_clause,[],[f263,f258,f84,f265])).
% 0.22/0.45  fof(f258,plain,(
% 0.22/0.45    spl6_32 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.45  fof(f263,plain,(
% 0.22/0.45    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_3 | ~spl6_32)),
% 0.22/0.45    inference(resolution,[],[f259,f85])).
% 0.22/0.45  fof(f259,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_32),
% 0.22/0.45    inference(avatar_component_clause,[],[f258])).
% 0.22/0.45  fof(f260,plain,(
% 0.22/0.45    spl6_9 | ~spl6_7 | spl6_32 | ~spl6_6 | ~spl6_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f256,f104,f96,f258,f100,f108])).
% 0.22/0.45  fof(f256,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK0) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) ) | (~spl6_6 | ~spl6_8)),
% 0.22/0.45    inference(resolution,[],[f203,f97])).
% 0.22/0.45  fof(f203,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X3,X4) | ~v1_funct_2(sK3,X4,X5) | k3_funct_2(X4,X5,sK3,X3) = k1_funct_1(sK3,X3) | v1_xboole_0(X4)) ) | ~spl6_8),
% 0.22/0.45    inference(resolution,[],[f68,f105])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    v1_funct_1(sK3) | ~spl6_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f104])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.45  fof(f244,plain,(
% 0.22/0.45    spl6_29 | ~spl6_3 | ~spl6_23 | ~spl6_24),
% 0.22/0.45    inference(avatar_split_clause,[],[f240,f206,f199,f84,f242])).
% 0.22/0.45  fof(f206,plain,(
% 0.22/0.45    spl6_24 <=> ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.45  fof(f240,plain,(
% 0.22/0.45    k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_3 | ~spl6_23 | ~spl6_24)),
% 0.22/0.45    inference(resolution,[],[f239,f85])).
% 0.22/0.45  fof(f239,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_23 | ~spl6_24)),
% 0.22/0.45    inference(resolution,[],[f207,f200])).
% 0.22/0.45  fof(f207,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)) ) | ~spl6_24),
% 0.22/0.45    inference(avatar_component_clause,[],[f206])).
% 0.22/0.45  fof(f238,plain,(
% 0.22/0.45    spl6_10 | ~spl6_2 | ~spl6_11 | ~spl6_28),
% 0.22/0.45    inference(avatar_split_clause,[],[f233,f228,f116,f80,f112])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    spl6_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.45  fof(f228,plain,(
% 0.22/0.45    spl6_28 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.45  fof(f233,plain,(
% 0.22/0.45    ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0) | (~spl6_11 | ~spl6_28)),
% 0.22/0.45    inference(resolution,[],[f229,f120])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1)) ) | ~spl6_11),
% 0.22/0.45    inference(resolution,[],[f55,f117])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0) | ~spl6_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f116])).
% 0.22/0.45  fof(f229,plain,(
% 0.22/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_28),
% 0.22/0.45    inference(avatar_component_clause,[],[f228])).
% 0.22/0.45  fof(f230,plain,(
% 0.22/0.45    spl6_28 | ~spl6_4 | ~spl6_21),
% 0.22/0.45    inference(avatar_split_clause,[],[f222,f182,f88,f228])).
% 0.22/0.45  fof(f182,plain,(
% 0.22/0.45    spl6_21 <=> k1_xboole_0 = sK2),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.45  fof(f222,plain,(
% 0.22/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_4 | ~spl6_21)),
% 0.22/0.45    inference(superposition,[],[f89,f183])).
% 0.22/0.45  fof(f183,plain,(
% 0.22/0.45    k1_xboole_0 = sK2 | ~spl6_21),
% 0.22/0.45    inference(avatar_component_clause,[],[f182])).
% 0.22/0.45  fof(f208,plain,(
% 0.22/0.45    spl6_10 | ~spl6_19 | spl6_24 | ~spl6_4 | ~spl6_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f204,f92,f88,f206,f173,f112])).
% 0.22/0.45  fof(f204,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | ~v1_funct_2(sK4,sK0,sK2) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) | v1_xboole_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.22/0.45    inference(resolution,[],[f202,f89])).
% 0.22/0.45  fof(f202,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK4,X1,X2) | k3_funct_2(X1,X2,sK4,X0) = k1_funct_1(sK4,X0) | v1_xboole_0(X1)) ) | ~spl6_5),
% 0.22/0.45    inference(resolution,[],[f68,f93])).
% 0.22/0.45  fof(f201,plain,(
% 0.22/0.45    spl6_9 | ~spl6_7 | spl6_23 | ~spl6_6 | ~spl6_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f195,f104,f96,f199,f100,f108])).
% 0.22/0.45  fof(f195,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK0) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | v1_xboole_0(sK1)) ) | (~spl6_6 | ~spl6_8)),
% 0.22/0.45    inference(resolution,[],[f168,f97])).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X3,X4) | ~v1_funct_2(sK3,X4,X5) | m1_subset_1(k3_funct_2(X4,X5,sK3,X3),X5) | v1_xboole_0(X4)) ) | ~spl6_8),
% 0.22/0.45    inference(resolution,[],[f67,f105])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    ~spl6_4 | ~spl6_18 | spl6_22),
% 0.22/0.45    inference(avatar_split_clause,[],[f190,f185,f162,f88])).
% 0.22/0.45  fof(f162,plain,(
% 0.22/0.45    spl6_18 <=> sK0 = k1_relat_1(sK4)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.45  fof(f185,plain,(
% 0.22/0.45    spl6_22 <=> sK0 = k1_relset_1(sK0,sK2,sK4)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.45  fof(f190,plain,(
% 0.22/0.45    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_18 | spl6_22)),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f189])).
% 0.22/0.45  fof(f189,plain,(
% 0.22/0.45    sK0 != sK0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_18 | spl6_22)),
% 0.22/0.45    inference(forward_demodulation,[],[f188,f163])).
% 0.22/0.45  fof(f163,plain,(
% 0.22/0.45    sK0 = k1_relat_1(sK4) | ~spl6_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f162])).
% 0.22/0.45  fof(f188,plain,(
% 0.22/0.45    sK0 != k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_22),
% 0.22/0.45    inference(superposition,[],[f186,f59])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.45  fof(f186,plain,(
% 0.22/0.45    sK0 != k1_relset_1(sK0,sK2,sK4) | spl6_22),
% 0.22/0.45    inference(avatar_component_clause,[],[f185])).
% 0.22/0.45  fof(f187,plain,(
% 0.22/0.45    ~spl6_4 | spl6_21 | ~spl6_22 | spl6_19),
% 0.22/0.45    inference(avatar_split_clause,[],[f179,f173,f185,f182,f88])).
% 0.22/0.45  fof(f179,plain,(
% 0.22/0.45    sK0 != k1_relset_1(sK0,sK2,sK4) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_19),
% 0.22/0.45    inference(resolution,[],[f174,f63])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(nnf_transformation,[],[f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(flattening,[],[f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    ~v1_funct_2(sK4,sK0,sK2) | spl6_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f173])).
% 0.22/0.45  fof(f165,plain,(
% 0.22/0.45    spl6_18 | ~spl6_2 | ~spl6_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f160,f88,f80,f162])).
% 0.22/0.45  fof(f160,plain,(
% 0.22/0.45    ~v1_partfun1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~spl6_4),
% 0.22/0.45    inference(resolution,[],[f157,f89])).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK4,X0) | k1_relat_1(sK4) = X0) ) | ~spl6_4),
% 0.22/0.45    inference(resolution,[],[f121,f89])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.22/0.45    inference(resolution,[],[f119,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.45    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.22/0.45    inference(resolution,[],[f56,f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(nnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    spl6_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f52,f116])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ~spl6_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f42,f112])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ~v1_xboole_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f38,f37,f36,f35,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) => (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.45    inference(negated_conjecture,[],[f12])).
% 0.22/0.45  fof(f12,conjecture,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    ~spl6_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f43,f108])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ~v1_xboole_0(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    spl6_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f44,f104])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    v1_funct_1(sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    spl6_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f45,f100])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    spl6_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f46,f96])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f94,plain,(
% 0.22/0.45    spl6_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f47,f92])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    v1_funct_1(sK4)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    spl6_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f48,f88])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    spl6_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f49,f84])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    m1_subset_1(sK5,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl6_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f50,f80])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    v1_partfun1(sK4,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    ~spl6_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f51,f76])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl6_1 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.45    inference(cnf_transformation,[],[f39])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (1580)------------------------------
% 0.22/0.45  % (1580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (1580)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (1580)Memory used [KB]: 10874
% 0.22/0.45  % (1580)Time elapsed: 0.043 s
% 0.22/0.45  % (1580)------------------------------
% 0.22/0.45  % (1580)------------------------------
% 0.22/0.46  % (1573)Success in time 0.092 s
%------------------------------------------------------------------------------
