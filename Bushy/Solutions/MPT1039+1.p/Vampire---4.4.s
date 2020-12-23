%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t154_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:32 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  374 (1047 expanded)
%              Number of leaves         :   76 ( 425 expanded)
%              Depth                    :   24
%              Number of atoms          : 1601 (4546 expanded)
%              Number of equality atoms :   55 ( 453 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f815,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f94,f101,f114,f121,f128,f135,f154,f168,f184,f191,f195,f241,f273,f280,f287,f294,f301,f312,f316,f329,f336,f340,f367,f371,f373,f384,f432,f457,f461,f473,f477,f507,f513,f533,f580,f587,f619,f626,f633,f640,f647,f654,f661,f668,f675,f682,f689,f698,f705,f715,f722,f735,f739,f755,f765,f769,f773,f789,f791,f798,f804,f814])).

fof(f814,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(avatar_contradiction_clause,[],[f813])).

fof(f813,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f812,f431])).

fof(f431,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl6_56
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f812,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f811,f86])).

fof(f86,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f811,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f810,f93])).

fof(f93,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f810,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f809,f100])).

fof(f100,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f809,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f808,f579])).

fof(f579,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f578])).

fof(f578,plain,
    ( spl6_76
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f808,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(duplicate_literal_removal,[],[f805])).

fof(f805,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(resolution,[],[f786,f77])).

fof(f77,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,sK4(k1_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',t162_partfun1)).

fof(f786,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f785,f431])).

fof(f785,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f784,f86])).

fof(f784,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f777])).

fof(f777,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f612,f76])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X3,sK4(k1_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f612,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,X1)
        | ~ v1_funct_1(X0) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f611,f252])).

fof(f252,plain,(
    ! [X10,X8,X9] :
      ( v1_funct_2(sK4(k1_xboole_0,X9,X8,X10),k1_xboole_0,X9)
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ r1_partfun1(X8,X10)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9))) ) ),
    inference(subsumption_resolution,[],[f251,f78])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( v1_partfun1(sK4(k1_xboole_0,X1,X2,X3),k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | v1_partfun1(sK4(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f251,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ r1_partfun1(X8,X10)
      | ~ v1_funct_1(X8)
      | ~ v1_partfun1(sK4(k1_xboole_0,X9,X8,X10),k1_xboole_0)
      | v1_funct_2(sK4(k1_xboole_0,X9,X8,X10),k1_xboole_0,X9) ) ),
    inference(subsumption_resolution,[],[f244,f80])).

fof(f80,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X2)
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f244,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ r1_partfun1(X8,X10)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_1(sK4(k1_xboole_0,X9,X8,X10))
      | ~ v1_partfun1(sK4(k1_xboole_0,X9,X8,X10),k1_xboole_0)
      | v1_funct_2(sK4(k1_xboole_0,X9,X8,X10),k1_xboole_0,X9) ) ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',cc1_funct_2)).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(sK4(k1_xboole_0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f611,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,X0,X1),k1_xboole_0,k1_xboole_0)
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,X1)
        | ~ v1_funct_1(X0) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f606,f80])).

fof(f606,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,X0,X1),k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(X0,X1)
        | ~ v1_funct_1(X0) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f573,f79])).

fof(f573,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X4,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ r1_partfun1(sK2,X4)
        | ~ r1_partfun1(sK3,X4) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f572,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f572,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X4,sK0,k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ r1_partfun1(sK2,X4)
        | ~ r1_partfun1(sK3,X4) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f107,f552])).

fof(f552,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(X4,sK0,k1_xboole_0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | ~ v1_funct_1(X4)
        | ~ r1_partfun1(sK2,X4)
        | ~ r1_partfun1(sK3,X4) )
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f534,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f534,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | ~ v1_funct_2(X4,sK0,sK1)
        | ~ v1_funct_1(X4)
        | ~ r1_partfun1(sK2,X4)
        | ~ r1_partfun1(sK3,X4) )
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f110,f45])).

fof(f45,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X4,sK0,sK1)
      | ~ v1_funct_1(X4)
      | ~ r1_partfun1(sK2,X4)
      | ~ r1_partfun1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',t154_funct_2)).

fof(f804,plain,
    ( spl6_110
    | ~ spl6_2
    | ~ spl6_50
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f767,f578,f331,f92,f763])).

fof(f763,plain,
    ( spl6_110
  <=> v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f331,plain,
    ( spl6_50
  <=> r1_partfun1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f767,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2))
    | ~ spl6_2
    | ~ spl6_50
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f766,f332])).

fof(f332,plain,
    ( r1_partfun1(sK2,sK2)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f331])).

fof(f766,plain,
    ( ~ r1_partfun1(sK2,sK2)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2))
    | ~ spl6_2
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f748,f93])).

fof(f748,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK2)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2))
    | ~ spl6_2
    | ~ spl6_76 ),
    inference(resolution,[],[f605,f579])).

fof(f605,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK2)
        | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X0,sK2)) )
    | ~ spl6_2
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f597,f93])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK2)
        | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X0,sK2)) )
    | ~ spl6_76 ),
    inference(resolution,[],[f579,f80])).

fof(f798,plain,
    ( spl6_108
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_36
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f753,f578,f430,f292,f92,f85,f720])).

fof(f720,plain,
    ( spl6_108
  <=> v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f292,plain,
    ( spl6_36
  <=> r1_partfun1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f753,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_36
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f752,f293])).

fof(f293,plain,
    ( r1_partfun1(sK3,sK2)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f292])).

fof(f752,plain,
    ( ~ r1_partfun1(sK3,sK2)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f747,f86])).

fof(f747,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK3,sK2)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2))
    | ~ spl6_2
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(resolution,[],[f605,f431])).

fof(f791,plain,
    ( spl6_104
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f737,f578,f430,f99,f92,f85,f703])).

fof(f703,plain,
    ( spl6_104
  <=> v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f737,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f736,f100])).

fof(f736,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f728,f93])).

fof(f728,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl6_0
    | ~ spl6_56
    | ~ spl6_76 ),
    inference(resolution,[],[f596,f579])).

fof(f596,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK3)
        | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X0,sK3)) )
    | ~ spl6_0
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f588,f86])).

fof(f588,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK3)
        | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X0,sK3)) )
    | ~ spl6_56 ),
    inference(resolution,[],[f431,f80])).

fof(f789,plain,
    ( spl6_100
    | ~ spl6_0
    | ~ spl6_16
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f733,f430,f143,f85,f687])).

fof(f687,plain,
    ( spl6_100
  <=> v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f143,plain,
    ( spl6_16
  <=> r1_partfun1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f733,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3))
    | ~ spl6_0
    | ~ spl6_16
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f732,f144])).

fof(f144,plain,
    ( r1_partfun1(sK3,sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f732,plain,
    ( ~ r1_partfun1(sK3,sK3)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3))
    | ~ spl6_0
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f727,f86])).

fof(f727,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK3,sK3)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3))
    | ~ spl6_0
    | ~ spl6_56 ),
    inference(resolution,[],[f596,f431])).

fof(f773,plain,
    ( ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_50
    | spl6_63
    | ~ spl6_76 ),
    inference(avatar_contradiction_clause,[],[f772])).

fof(f772,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_50
    | ~ spl6_63
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f771,f767])).

fof(f771,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f770,f107])).

fof(f770,plain,
    ( ~ v1_funct_1(sK4(sK0,k1_xboole_0,sK2,sK2))
    | ~ spl6_8
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f469,f110])).

fof(f469,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1,sK2,sK2))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl6_63
  <=> ~ v1_funct_1(sK4(sK0,sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f769,plain,
    ( ~ spl6_2
    | ~ spl6_50
    | ~ spl6_76
    | spl6_111 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_50
    | ~ spl6_76
    | ~ spl6_111 ),
    inference(subsumption_resolution,[],[f761,f767])).

fof(f761,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2))
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl6_111
  <=> ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f765,plain,
    ( spl6_110
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f567,f471,f109,f106,f763])).

fof(f471,plain,
    ( spl6_62
  <=> v1_funct_1(sK4(sK0,sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f567,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK2))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_62 ),
    inference(backward_demodulation,[],[f107,f547])).

fof(f547,plain,
    ( v1_funct_1(sK4(sK0,k1_xboole_0,sK2,sK2))
    | ~ spl6_8
    | ~ spl6_62 ),
    inference(backward_demodulation,[],[f110,f472])).

fof(f472,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2,sK2))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f471])).

fof(f755,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_36
    | ~ spl6_56
    | ~ spl6_76
    | spl6_109 ),
    inference(avatar_contradiction_clause,[],[f754])).

fof(f754,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_36
    | ~ spl6_56
    | ~ spl6_76
    | ~ spl6_109 ),
    inference(subsumption_resolution,[],[f753,f718])).

fof(f718,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2))
    | ~ spl6_109 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl6_109
  <=> ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f739,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56
    | ~ spl6_76
    | spl6_105 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56
    | ~ spl6_76
    | ~ spl6_105 ),
    inference(subsumption_resolution,[],[f737,f701])).

fof(f701,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl6_105 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl6_105
  <=> ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f735,plain,
    ( ~ spl6_0
    | ~ spl6_16
    | ~ spl6_56
    | spl6_101 ),
    inference(avatar_contradiction_clause,[],[f734])).

fof(f734,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_16
    | ~ spl6_56
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f733,f685])).

fof(f685,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3))
    | ~ spl6_101 ),
    inference(avatar_component_clause,[],[f684])).

fof(f684,plain,
    ( spl6_101
  <=> ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f722,plain,
    ( spl6_108
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f566,f455,f109,f106,f720])).

fof(f455,plain,
    ( spl6_58
  <=> v1_funct_1(sK4(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f566,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK2))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_58 ),
    inference(backward_demodulation,[],[f107,f546])).

fof(f546,plain,
    ( v1_funct_1(sK4(sK0,k1_xboole_0,sK3,sK2))
    | ~ spl6_8
    | ~ spl6_58 ),
    inference(backward_demodulation,[],[f110,f456])).

fof(f456,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK3,sK2))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f455])).

fof(f715,plain,
    ( ~ spl6_107
    | ~ spl6_6
    | ~ spl6_8
    | spl6_73 ),
    inference(avatar_split_clause,[],[f571,f505,f109,f106,f713])).

fof(f713,plain,
    ( spl6_107
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f505,plain,
    ( spl6_73
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f571,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_73 ),
    inference(backward_demodulation,[],[f107,f551])).

fof(f551,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))),sK0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_73 ),
    inference(backward_demodulation,[],[f110,f506])).

fof(f506,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f505])).

fof(f705,plain,
    ( spl6_104
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f565,f382,f109,f106,f703])).

fof(f382,plain,
    ( spl6_54
  <=> v1_funct_1(sK4(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f565,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_54 ),
    inference(backward_demodulation,[],[f107,f545])).

fof(f545,plain,
    ( v1_funct_1(sK4(sK0,k1_xboole_0,sK2,sK3))
    | ~ spl6_8
    | ~ spl6_54 ),
    inference(backward_demodulation,[],[f110,f383])).

fof(f383,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f382])).

fof(f698,plain,
    ( ~ spl6_103
    | ~ spl6_6
    | ~ spl6_8
    | spl6_69 ),
    inference(avatar_split_clause,[],[f569,f493,f109,f106,f696])).

fof(f696,plain,
    ( spl6_103
  <=> ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f493,plain,
    ( spl6_69
  <=> ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f569,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_69 ),
    inference(backward_demodulation,[],[f107,f549])).

fof(f549,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))
    | ~ spl6_8
    | ~ spl6_69 ),
    inference(backward_demodulation,[],[f110,f494])).

fof(f494,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f493])).

fof(f689,plain,
    ( spl6_100
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f418,f365,f109,f106,f687])).

fof(f365,plain,
    ( spl6_52
  <=> v1_funct_1(sK4(sK0,sK1,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f418,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK3,sK3))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f107,f400])).

fof(f400,plain,
    ( v1_funct_1(sK4(sK0,k1_xboole_0,sK3,sK3))
    | ~ spl6_8
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f110,f366])).

fof(f366,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK3,sK3))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f365])).

fof(f682,plain,
    ( ~ spl6_99
    | ~ spl6_6
    | ~ spl6_8
    | spl6_67 ),
    inference(avatar_split_clause,[],[f568,f487,f109,f106,f680])).

fof(f680,plain,
    ( spl6_99
  <=> ~ r1_partfun1(sK3,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f487,plain,
    ( spl6_67
  <=> ~ r1_partfun1(sK3,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f568,plain,
    ( ~ r1_partfun1(sK3,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_67 ),
    inference(backward_demodulation,[],[f107,f548])).

fof(f548,plain,
    ( ~ r1_partfun1(sK3,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))
    | ~ spl6_8
    | ~ spl6_67 ),
    inference(backward_demodulation,[],[f110,f488])).

fof(f488,plain,
    ( ~ r1_partfun1(sK3,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f487])).

fof(f675,plain,
    ( ~ spl6_97
    | ~ spl6_6
    | ~ spl6_8
    | spl6_71 ),
    inference(avatar_split_clause,[],[f570,f499,f109,f106,f673])).

fof(f673,plain,
    ( spl6_97
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f499,plain,
    ( spl6_71
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f570,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_71 ),
    inference(backward_demodulation,[],[f107,f550])).

fof(f550,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))
    | ~ spl6_8
    | ~ spl6_71 ),
    inference(backward_demodulation,[],[f110,f500])).

fof(f500,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f499])).

fof(f668,plain,
    ( ~ spl6_95
    | ~ spl6_6
    | ~ spl6_8
    | spl6_47 ),
    inference(avatar_split_clause,[],[f417,f318,f109,f106,f666])).

fof(f666,plain,
    ( spl6_95
  <=> ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f318,plain,
    ( spl6_47
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f417,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_47 ),
    inference(backward_demodulation,[],[f107,f399])).

fof(f399,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_47 ),
    inference(backward_demodulation,[],[f110,f319])).

fof(f319,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f318])).

fof(f661,plain,
    ( ~ spl6_93
    | ~ spl6_6
    | ~ spl6_8
    | spl6_41 ),
    inference(avatar_split_clause,[],[f416,f307,f109,f106,f659])).

fof(f659,plain,
    ( spl6_93
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f307,plain,
    ( spl6_41
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f416,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f107,f398])).

fof(f398,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f110,f308])).

fof(f308,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f307])).

fof(f654,plain,
    ( ~ spl6_91
    | ~ spl6_6
    | ~ spl6_8
    | spl6_19 ),
    inference(avatar_split_clause,[],[f413,f152,f109,f106,f652])).

fof(f652,plain,
    ( spl6_91
  <=> ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f152,plain,
    ( spl6_19
  <=> ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f413,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f107,f391])).

fof(f391,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f110,f153])).

fof(f153,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f647,plain,
    ( ~ spl6_89
    | ~ spl6_6
    | spl6_49 ),
    inference(avatar_split_clause,[],[f410,f327,f106,f645])).

fof(f645,plain,
    ( spl6_89
  <=> ~ v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f327,plain,
    ( spl6_49
  <=> ~ v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f410,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_49 ),
    inference(backward_demodulation,[],[f107,f328])).

fof(f328,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f327])).

fof(f640,plain,
    ( ~ spl6_87
    | ~ spl6_6
    | spl6_39 ),
    inference(avatar_split_clause,[],[f409,f299,f106,f638])).

fof(f638,plain,
    ( spl6_87
  <=> ~ v1_partfun1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f299,plain,
    ( spl6_39
  <=> ~ v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f409,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_39 ),
    inference(backward_demodulation,[],[f107,f300])).

fof(f300,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f299])).

fof(f633,plain,
    ( spl6_84
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f408,f271,f106,f631])).

fof(f631,plain,
    ( spl6_84
  <=> v4_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f271,plain,
    ( spl6_30
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f408,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f107,f272])).

fof(f272,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f271])).

fof(f626,plain,
    ( spl6_82
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f407,f239,f106,f624])).

fof(f624,plain,
    ( spl6_82
  <=> v4_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f239,plain,
    ( spl6_28
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f407,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f107,f240])).

fof(f240,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f239])).

fof(f619,plain,
    ( spl6_80
    | ~ spl6_8
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f397,f285,f109,f617])).

fof(f617,plain,
    ( spl6_80
  <=> v5_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f285,plain,
    ( spl6_34
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f397,plain,
    ( v5_relat_1(sK2,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f110,f286])).

fof(f286,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f285])).

fof(f587,plain,
    ( spl6_78
    | ~ spl6_8
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f396,f278,f109,f585])).

fof(f585,plain,
    ( spl6_78
  <=> v5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f278,plain,
    ( spl6_32
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f396,plain,
    ( v5_relat_1(sK3,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f110,f279])).

fof(f279,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f580,plain,
    ( spl6_76
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f412,f126,f109,f106,f578])).

fof(f126,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f412,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f107,f389])).

fof(f389,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f110,f127])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f533,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f531,f86])).

fof(f531,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f530,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f530,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f529,f120])).

fof(f120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f529,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f528,f127])).

fof(f528,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f527,f93])).

fof(f527,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f526,f293])).

fof(f526,plain,
    ( ~ r1_partfun1(sK3,sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(duplicate_literal_removal,[],[f525])).

fof(f525,plain,
    ( ~ r1_partfun1(sK3,sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK3,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(resolution,[],[f520,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X3,sK4(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f520,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(sK0,sK1,sK3,X0))
        | ~ r1_partfun1(sK3,X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f519,f113])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(sK0,sK1,sK3,X0))
        | ~ r1_partfun1(sK3,X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1 )
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f518,f86])).

fof(f518,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(sK0,sK1,sK3,X0))
        | ~ v1_funct_1(sK3)
        | ~ r1_partfun1(sK3,X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1 )
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f517,f120])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK3,X0))
        | ~ v1_funct_1(sK3)
        | ~ r1_partfun1(sK3,X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1 )
    | ~ spl6_74 ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK3,X0))
        | ~ v1_funct_1(sK3)
        | ~ r1_partfun1(sK3,X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(sK3,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_74 ),
    inference(resolution,[],[f512,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,sK4(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f512,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(sK3,sK4(sK0,sK1,X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0,X1))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,X1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f511])).

fof(f511,plain,
    ( spl6_74
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_partfun1(sK3,sK4(sK0,sK1,X0,X1))
        | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0,X1))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,X1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f513,plain,
    ( spl6_8
    | spl6_74 ),
    inference(avatar_split_clause,[],[f386,f511,f109])).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0,X1))
      | ~ r1_partfun1(sK3,sK4(sK0,sK1,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f385,f266])).

fof(f266,plain,(
    ! [X10,X8,X7,X9] :
      ( v1_funct_2(sK4(X8,X9,X7,X10),X8,X9)
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_xboole_0 = X9
      | ~ r1_partfun1(X7,X10)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ),
    inference(subsumption_resolution,[],[f265,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK4(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f265,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_xboole_0 = X9
      | ~ r1_partfun1(X7,X10)
      | ~ v1_funct_1(X7)
      | ~ v1_partfun1(sK4(X8,X9,X7,X10),X8)
      | v1_funct_2(sK4(X8,X9,X7,X10),X8,X9) ) ),
    inference(subsumption_resolution,[],[f255,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f255,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_xboole_0 = X9
      | ~ r1_partfun1(X7,X10)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_1(sK4(X8,X9,X7,X10))
      | ~ v1_partfun1(sK4(X8,X9,X7,X10),X8)
      | v1_funct_2(sK4(X8,X9,X7,X10),X8,X9) ) ),
    inference(resolution,[],[f59,f52])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f385,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK4(sK0,sK1,X0,X1),sK0,sK1)
      | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0,X1))
      | ~ r1_partfun1(sK3,sK4(sK0,sK1,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f253,f58])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK4(sK0,sK1,X0,X1),sK0,sK1)
      | ~ v1_funct_1(sK4(sK0,sK1,X0,X1))
      | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0,X1))
      | ~ r1_partfun1(sK3,sK4(sK0,sK1,X0,X1)) ) ),
    inference(resolution,[],[f59,f45])).

fof(f507,plain,
    ( ~ spl6_67
    | ~ spl6_69
    | ~ spl6_71
    | ~ spl6_73 ),
    inference(avatar_split_clause,[],[f138,f505,f499,f493,f487])).

fof(f138,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1)
    | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ r1_partfun1(sK3,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    inference(resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',existence_m1_subset_1)).

fof(f477,plain,
    ( spl6_8
    | spl6_64
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f223,f126,f92,f475,f109])).

fof(f475,plain,
    ( spl6_64
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | v1_funct_1(sK4(sK0,sK1,X1,sK2))
        | ~ r1_partfun1(X1,sK2)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f223,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(X1,sK2)
        | v1_funct_1(sK4(sK0,sK1,X1,sK2)) )
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f219,f93])).

fof(f219,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(X1,sK2)
        | v1_funct_1(sK4(sK0,sK1,X1,sK2)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f58,f127])).

fof(f473,plain,
    ( spl6_62
    | ~ spl6_2
    | spl6_9
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f359,f331,f126,f112,f92,f471])).

fof(f359,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2,sK2))
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f358,f332])).

fof(f358,plain,
    ( ~ r1_partfun1(sK2,sK2)
    | v1_funct_1(sK4(sK0,sK1,sK2,sK2))
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f353,f93])).

fof(f353,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK2)
    | v1_funct_1(sK4(sK0,sK1,sK2,sK2))
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(resolution,[],[f224,f127])).

fof(f224,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2)
        | v1_funct_1(sK4(sK0,sK1,X1,sK2)) )
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f223,f113])).

fof(f461,plain,
    ( spl6_8
    | spl6_60
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f221,f119,f85,f459,f109])).

fof(f459,plain,
    ( spl6_60
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | v1_funct_1(sK4(sK0,sK1,X0,sK3))
        | ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(X0,sK3)
        | v1_funct_1(sK4(sK0,sK1,X0,sK3)) )
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f218,f86])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(X0,sK3)
        | v1_funct_1(sK4(sK0,sK1,X0,sK3)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f58,f120])).

fof(f457,plain,
    ( spl6_58
    | ~ spl6_0
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f357,f292,f126,f119,f112,f92,f85,f455])).

fof(f357,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK3,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f356,f293])).

fof(f356,plain,
    ( ~ r1_partfun1(sK3,sK2)
    | v1_funct_1(sK4(sK0,sK1,sK3,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f352,f86])).

fof(f352,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK3,sK2)
    | v1_funct_1(sK4(sK0,sK1,sK3,sK2))
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f224,f120])).

fof(f432,plain,
    ( spl6_56
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f411,f119,f109,f106,f430])).

fof(f411,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f107,f388])).

fof(f388,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f110,f120])).

fof(f384,plain,
    ( spl6_54
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f350,f126,f119,f112,f99,f92,f85,f382])).

fof(f350,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f349,f100])).

fof(f349,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f344,f93])).

fof(f344,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f222,f127])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK3)
        | v1_funct_1(sK4(sK0,sK1,X0,sK3)) )
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f221,f113])).

fof(f373,plain,
    ( ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f369,f93])).

fof(f369,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(resolution,[],[f187,f183])).

fof(f183,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_22
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_24
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f371,plain,
    ( ~ spl6_0
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f368,f86])).

fof(f368,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(resolution,[],[f187,f167])).

fof(f167,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f367,plain,
    ( spl6_52
    | ~ spl6_0
    | spl6_9
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f348,f143,f119,f112,f85,f365])).

fof(f348,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK3,sK3))
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f347,f144])).

fof(f347,plain,
    ( ~ r1_partfun1(sK3,sK3)
    | v1_funct_1(sK4(sK0,sK1,sK3,sK3))
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f343,f86])).

fof(f343,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK3,sK3)
    | v1_funct_1(sK4(sK0,sK1,sK3,sK3))
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f222,f120])).

fof(f340,plain,
    ( ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26
    | spl6_51 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f338,f93])).

fof(f338,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f337,f183])).

fof(f337,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl6_26
    | ~ spl6_51 ),
    inference(resolution,[],[f335,f190])).

fof(f190,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_26
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_partfun1(X0,X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f335,plain,
    ( ~ r1_partfun1(sK2,sK2)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl6_51
  <=> ~ r1_partfun1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f336,plain,
    ( ~ spl6_37
    | ~ spl6_51
    | ~ spl6_47
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f141,f126,f92,f318,f334,f289])).

fof(f289,plain,
    ( spl6_37
  <=> ~ r1_partfun1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f141,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_partfun1(sK2,sK2)
    | ~ r1_partfun1(sK3,sK2)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f137,f93])).

fof(f137,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK2)
    | ~ r1_partfun1(sK3,sK2)
    | ~ spl6_12 ),
    inference(resolution,[],[f45,f127])).

fof(f329,plain,
    ( spl6_46
    | ~ spl6_49
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f208,f126,f92,f327,f321])).

fof(f321,plain,
    ( spl6_46
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f208,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f204,f93])).

fof(f204,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_partfun1(sK2,sK0)
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f52,f127])).

fof(f316,plain,
    ( ~ spl6_41
    | spl6_44
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f160,f126,f314,f307])).

fof(f314,plain,
    ( spl6_44
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f160,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f68,f127])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',t5_subset)).

fof(f312,plain,
    ( ~ spl6_41
    | spl6_42
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f159,f119,f310,f307])).

fof(f310,plain,
    ( spl6_42
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f68,f120])).

fof(f301,plain,
    ( ~ spl6_39
    | ~ spl6_0
    | ~ spl6_10
    | spl6_19 ),
    inference(avatar_split_clause,[],[f207,f152,f119,f85,f299])).

fof(f207,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f206,f153])).

fof(f206,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f203,f86])).

fof(f203,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_partfun1(sK3,sK0)
    | v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f52,f120])).

fof(f294,plain,
    ( spl6_36
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f202,f182,f166,f99,f92,f85,f292])).

fof(f202,plain,
    ( r1_partfun1(sK3,sK2)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f201,f183])).

fof(f201,plain,
    ( ~ v1_relat_1(sK2)
    | r1_partfun1(sK3,sK2)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f200,f86])).

fof(f200,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK3,sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f199,f167])).

fof(f199,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK3,sK2)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f196,f93])).

fof(f196,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK3,sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f63,f100])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( r1_partfun1(X0,X1)
       => r1_partfun1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',symmetry_r1_partfun1)).

fof(f287,plain,
    ( spl6_34
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f173,f126,f285])).

fof(f173,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f75,f127])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',cc2_relset_1)).

fof(f280,plain,
    ( spl6_32
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f172,f119,f278])).

fof(f172,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f75,f120])).

fof(f273,plain,
    ( spl6_30
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f170,f126,f271])).

fof(f170,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f74,f127])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f241,plain,
    ( spl6_28
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f169,f119,f239])).

fof(f169,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f74,f120])).

fof(f195,plain,
    ( ~ spl6_0
    | spl6_17
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f193,f86])).

fof(f193,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f192,f167])).

fof(f192,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl6_17
    | ~ spl6_26 ),
    inference(resolution,[],[f190,f147])).

fof(f147,plain,
    ( ~ r1_partfun1(sK3,sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_17
  <=> ~ r1_partfun1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f191,plain,
    ( spl6_24
    | spl6_26 ),
    inference(avatar_split_clause,[],[f64,f189,f186])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_partfun1(X0,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_partfun1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',reflexivity_r1_partfun1)).

fof(f184,plain,
    ( spl6_22
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f156,f126,f182])).

fof(f156,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_12 ),
    inference(resolution,[],[f70,f127])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',cc1_relset_1)).

fof(f168,plain,
    ( spl6_20
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f155,f119,f166])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f70,f120])).

fof(f154,plain,
    ( ~ spl6_17
    | ~ spl6_19
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f140,f119,f99,f85,f152,f146])).

fof(f140,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ r1_partfun1(sK3,sK3)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f139,f100])).

fof(f139,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK3,sK3)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f136,f86])).

fof(f136,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK3,sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f45,f120])).

fof(f135,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f67,f133])).

fof(f133,plain,
    ( spl6_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f67,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t154_funct_2.p',d2_xboole_0)).

fof(f128,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f51,f126])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f121,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,
    ( spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f46,f112,f106])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f50,f92])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
