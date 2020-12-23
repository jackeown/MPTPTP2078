%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:00 EST 2020

% Result     : Theorem 19.02s
% Output     : Refutation 19.64s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 499 expanded)
%              Number of leaves         :   47 ( 181 expanded)
%              Depth                    :   16
%              Number of atoms          :  952 (1894 expanded)
%              Number of equality atoms :  216 ( 524 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f146,f151,f370,f373,f629,f722,f770,f774,f1827,f1889,f4784,f4843,f4856,f5154,f5354,f5362,f5400,f14167,f14189,f16703,f16758,f16771,f16781,f20077,f20189,f21198])).

fof(f21198,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | spl7_45
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(avatar_contradiction_clause,[],[f21197])).

fof(f21197,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | spl7_45
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f21196,f125])).

fof(f125,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_1
  <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f21196,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | spl7_45
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(equality_resolution,[],[f21188])).

fof(f21188,plain,
    ( ! [X21] :
        ( sK3 != X21
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21) )
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | spl7_45
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f21164,f609])).

fof(f609,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl7_45
  <=> k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f21164,plain,
    ( ! [X21] :
        ( sK3 != X21
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21) )
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(duplicate_literal_removal,[],[f21161])).

fof(f21161,plain,
    ( ! [X21] :
        ( sK3 != X21
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21) )
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(superposition,[],[f81,f20450])).

fof(f20450,plain,
    ( ! [X2] :
        ( sK3 = sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl7_2
    | ~ spl7_4
    | spl7_25
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f20449,f6266])).

fof(f6266,plain,
    ( ! [X24] :
        ( v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24) )
    | spl7_25
    | ~ spl7_46
    | ~ spl7_59
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f6265,f786])).

fof(f786,plain,
    ( ! [X2] :
        ( v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1))
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl7_59
  <=> ! [X2] :
        ( v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1))
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f6265,plain,
    ( ! [X24] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24)
        | v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0)
        | ~ v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0,k1_tarski(sK1)) )
    | spl7_25
    | ~ spl7_46
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f6264,f613])).

fof(f613,plain,
    ( ! [X0] :
        ( v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f612])).

fof(f612,plain,
    ( spl7_46
  <=> ! [X0] :
        ( v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f6264,plain,
    ( ! [X24] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24)
        | v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0)
        | ~ v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24)) )
    | spl7_25
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f6234,f312])).

fof(f312,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl7_25
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f6234,plain,
    ( ! [X24] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24)
        | k1_xboole_0 = k1_tarski(sK1)
        | v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0)
        | ~ v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24)) )
    | ~ spl7_61 ),
    inference(resolution,[],[f826,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f826,plain,
    ( ! [X2] :
        ( m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f825])).

fof(f825,plain,
    ( spl7_61
  <=> ! [X2] :
        ( m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f20449,plain,
    ( ! [X2] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)
        | sK3 = sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)
        | ~ v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_46
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f20419,f613])).

fof(f20419,plain,
    ( ! [X2] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)
        | ~ v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2))
        | sK3 = sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)
        | ~ v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_61
    | ~ spl7_245 ),
    inference(resolution,[],[f826,f7899])).

fof(f7899,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f5379,f532])).

fof(f532,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f524,f140])).

fof(f140,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f524,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f97,f130])).

fof(f130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f5379,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0) )
    | ~ spl7_245 ),
    inference(avatar_component_clause,[],[f5378])).

fof(f5378,plain,
    ( spl7_245
  <=> ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_245])])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f20189,plain,
    ( spl7_61
    | ~ spl7_5
    | ~ spl7_6
    | spl7_45 ),
    inference(avatar_split_clause,[],[f20188,f608,f148,f143,f825])).

fof(f143,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f148,plain,
    ( spl7_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f20188,plain,
    ( ! [X4] :
        ( m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X4),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X4) )
    | ~ spl7_5
    | ~ spl7_6
    | spl7_45 ),
    inference(subsumption_resolution,[],[f20186,f609])).

fof(f20186,plain,
    ( ! [X4] :
        ( m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X4),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X4) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f518,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f518,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f510,f150])).

fof(f150,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f510,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f93,f145])).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f20077,plain,
    ( spl7_245
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f20076,f471,f138,f128,f5378])).

fof(f471,plain,
    ( spl7_34
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f20076,plain,
    ( ! [X10] :
        ( ~ r1_partfun1(X10,sK3)
        | ~ v1_partfun1(X10,sK0)
        | sK3 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X10) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f20075,f140])).

fof(f20075,plain,
    ( ! [X10] :
        ( ~ r1_partfun1(X10,sK3)
        | ~ v1_partfun1(X10,sK0)
        | sK3 = X10
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X10) )
    | ~ spl7_2
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f20030,f473])).

fof(f473,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f471])).

fof(f20030,plain,
    ( ! [X10] :
        ( ~ r1_partfun1(X10,sK3)
        | ~ v1_partfun1(sK3,sK0)
        | ~ v1_partfun1(X10,sK0)
        | sK3 = X10
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X10) )
    | ~ spl7_2 ),
    inference(resolution,[],[f130,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f16781,plain,
    ( ~ spl7_11
    | spl7_12
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f16776,f163,f187,f183])).

fof(f183,plain,
    ( spl7_11
  <=> r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f187,plain,
    ( spl7_12
  <=> sK2 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f163,plain,
    ( spl7_8
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f16776,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f165,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f165,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f16771,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f16763,f158,f178,f174])).

fof(f174,plain,
    ( spl7_9
  <=> r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f178,plain,
    ( spl7_10
  <=> k2_zfmisc_1(sK0,k1_tarski(sK1)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f158,plain,
    ( spl7_7
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f16763,plain,
    ( k2_zfmisc_1(sK0,k1_tarski(sK1)) = sK3
    | ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f160,f87])).

fof(f160,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f16758,plain,
    ( spl7_8
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f16726,f143,f163])).

fof(f16726,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | ~ spl7_5 ),
    inference(resolution,[],[f145,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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

fof(f16703,plain,
    ( spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f16650,f128,f158])).

fof(f16650,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | ~ spl7_2 ),
    inference(resolution,[],[f130,f98])).

fof(f14189,plain,
    ( spl7_59
    | ~ spl7_5
    | ~ spl7_6
    | spl7_45 ),
    inference(avatar_split_clause,[],[f14188,f608,f148,f143,f785])).

fof(f14188,plain,
    ( ! [X2] :
        ( v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1))
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl7_5
    | ~ spl7_6
    | spl7_45 ),
    inference(subsumption_resolution,[],[f14186,f609])).

fof(f14186,plain,
    ( ! [X2] :
        ( v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f455,f80])).

fof(f455,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X1,sK0,k1_tarski(sK1)) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f448,f150])).

fof(f448,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f92,f145])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14167,plain,
    ( spl7_45
    | spl7_46
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f14165,f148,f143,f612,f608])).

fof(f14165,plain,
    ( ! [X2] :
        ( v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f337,f80])).

fof(f337,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f330,f150])).

fof(f330,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f91,f145])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5400,plain,
    ( spl7_25
    | ~ spl7_3
    | spl7_34
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f5399,f158,f138,f471,f133,f311])).

fof(f133,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f5399,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f3240,f140])).

fof(f3240,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f160,f463])).

fof(f463,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X2))
      | v1_partfun1(X3,X4)
      | ~ v1_funct_2(X3,X4,X2)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f120,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5362,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK3
    | sK2 != k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k2_zfmisc_1(sK0,k1_tarski(sK1)) != sK3
    | r2_hidden(sK3,k1_xboole_0)
    | ~ r2_hidden(sK1,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5354,plain,
    ( spl7_244
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f5347,f311,f5351])).

fof(f5351,plain,
    ( spl7_244
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).

fof(f5347,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_25 ),
    inference(resolution,[],[f5173,f169])).

fof(f169,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f87,f104])).

% (2477)Time limit reached!
% (2477)------------------------------
% (2477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2477)Termination reason: Time limit
% (2477)Termination phase: Saturation

% (2477)Memory used [KB]: 15095
% (2477)Time elapsed: 2.426 s
% (2477)------------------------------
% (2477)------------------------------
fof(f104,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f5173,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl7_25 ),
    inference(resolution,[],[f4853,f98])).

fof(f4853,plain,
    ( ! [X37] : m1_subset_1(sK1,X37)
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f4776,f104])).

fof(f4776,plain,
    ( ! [X37] :
        ( ~ r1_tarski(k1_xboole_0,X37)
        | m1_subset_1(sK1,X37) )
    | ~ spl7_25 ),
    inference(superposition,[],[f869,f313])).

fof(f313,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f311])).

fof(f869,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k1_tarski(X6),X7)
      | m1_subset_1(X6,X7) ) ),
    inference(resolution,[],[f196,f152])).

fof(f152,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f108,f90])).

fof(f90,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f108,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f196,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,X6)
      | m1_subset_1(X4,X5)
      | ~ r1_tarski(X6,X5) ) ),
    inference(resolution,[],[f96,f99])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f5154,plain,
    ( spl7_62
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f5153,f260,f833])).

fof(f833,plain,
    ( spl7_62
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f260,plain,
    ( spl7_18
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f5153,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f5151,f104])).

fof(f5151,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f262,f87])).

fof(f262,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f260])).

fof(f4856,plain,
    ( spl7_13
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f4762,f311,f233])).

fof(f233,plain,
    ( spl7_13
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f4762,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_25 ),
    inference(superposition,[],[f152,f313])).

fof(f4843,plain,
    ( spl7_23
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f4842,f311,f291])).

fof(f291,plain,
    ( spl7_23
  <=> ! [X3] : k1_xboole_0 = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f4842,plain,
    ( ! [X1] : k1_xboole_0 = X1
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f4759,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f4759,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl7_25 ),
    inference(superposition,[],[f89,f313])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f4784,plain,
    ( spl7_18
    | ~ spl7_7
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f4783,f311,f158,f260])).

fof(f4783,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f4729,f115])).

fof(f4729,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl7_7
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f160,f313])).

fof(f1889,plain,
    ( ~ spl7_23
    | spl7_25 ),
    inference(avatar_contradiction_clause,[],[f1888])).

fof(f1888,plain,
    ( $false
    | ~ spl7_23
    | spl7_25 ),
    inference(subsumption_resolution,[],[f1748,f292])).

fof(f292,plain,
    ( ! [X3] : k1_xboole_0 = X3
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f291])).

fof(f1748,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | ~ spl7_23
    | spl7_25 ),
    inference(backward_demodulation,[],[f312,f292])).

fof(f1827,plain,
    ( ~ spl7_23
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f1826])).

fof(f1826,plain,
    ( $false
    | ~ spl7_23
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1704,f292])).

fof(f1704,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,sK2)
    | ~ spl7_23
    | spl7_45 ),
    inference(backward_demodulation,[],[f609,f292])).

fof(f774,plain,
    ( spl7_23
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f773,f619,f291])).

fof(f619,plain,
    ( spl7_47
  <=> k1_xboole_0 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f773,plain,
    ( ! [X1] : k1_xboole_0 = X1
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f764,f115])).

fof(f764,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl7_47 ),
    inference(superposition,[],[f89,f620])).

fof(f620,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f619])).

fof(f770,plain,
    ( ~ spl7_45
    | spl7_1
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f762,f619,f123,f608])).

fof(f762,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | spl7_1
    | ~ spl7_47 ),
    inference(backward_demodulation,[],[f125,f620])).

fof(f722,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_25
    | ~ spl7_45
    | spl7_48 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_25
    | ~ spl7_45
    | spl7_48 ),
    inference(subsumption_resolution,[],[f720,f628])).

fof(f628,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl7_48
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f720,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_25
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f719,f610])).

fof(f610,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f608])).

fof(f719,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_25 ),
    inference(subsumption_resolution,[],[f709,f150])).

fof(f709,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_25 ),
    inference(resolution,[],[f692,f145])).

fof(f692,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_25 ),
    inference(subsumption_resolution,[],[f584,f532])).

fof(f584,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_25 ),
    inference(subsumption_resolution,[],[f583,f140])).

fof(f583,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | spl7_25 ),
    inference(subsumption_resolution,[],[f582,f135])).

fof(f135,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | spl7_25 ),
    inference(subsumption_resolution,[],[f573,f312])).

fof(f573,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r1_partfun1(X0,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f70,f130])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f629,plain,
    ( ~ spl7_48
    | spl7_47 ),
    inference(avatar_split_clause,[],[f624,f619,f626])).

fof(f624,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | spl7_47 ),
    inference(trivial_inequality_removal,[],[f623])).

fof(f623,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK3,k1_xboole_0)
    | spl7_47 ),
    inference(superposition,[],[f621,f211])).

fof(f211,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_tarski(X2)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f168,f169])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f100,f98])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f621,plain,
    ( k1_xboole_0 != k1_tarski(sK3)
    | spl7_47 ),
    inference(avatar_component_clause,[],[f619])).

fof(f373,plain,
    ( spl7_11
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl7_11
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f371,f104])).

fof(f371,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl7_11
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f349,f115])).

fof(f349,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | spl7_11
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f185,f313])).

fof(f185,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f370,plain,
    ( spl7_9
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl7_9
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f368,f104])).

fof(f368,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl7_9
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f348,f115])).

fof(f348,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | spl7_9
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f176,f313])).

fof(f176,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f151,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f58,f148])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f146,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f59,f143])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f141,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f60,f138])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f136,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f61,f133])).

fof(f61,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f131,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f62,f128])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f126,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f63,f123])).

fof(f63,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2469)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (2485)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (2477)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (2470)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (2467)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (2463)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (2466)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (2464)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (2465)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (2491)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (2479)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (2488)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (2490)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (2482)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (2480)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (2483)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.55  % (2471)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.55  % (2489)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.55  % (2481)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.55  % (2474)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.55  % (2472)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.55  % (2462)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.55  % (2491)Refutation not found, incomplete strategy% (2491)------------------------------
% 1.31/0.55  % (2491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (2491)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (2491)Memory used [KB]: 1791
% 1.31/0.55  % (2491)Time elapsed: 0.141 s
% 1.31/0.55  % (2491)------------------------------
% 1.31/0.55  % (2491)------------------------------
% 1.31/0.56  % (2473)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.56  % (2475)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.56  % (2487)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.56  % (2486)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.56  % (2489)Refutation not found, incomplete strategy% (2489)------------------------------
% 1.31/0.56  % (2489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (2489)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (2489)Memory used [KB]: 6268
% 1.31/0.56  % (2489)Time elapsed: 0.148 s
% 1.31/0.56  % (2489)------------------------------
% 1.31/0.56  % (2489)------------------------------
% 1.31/0.57  % (2478)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.58  % (2484)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.58  % (2476)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.57/0.58  % (2478)Refutation not found, incomplete strategy% (2478)------------------------------
% 1.57/0.58  % (2478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (2468)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.59  % (2486)Refutation not found, incomplete strategy% (2486)------------------------------
% 1.57/0.59  % (2486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (2486)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (2486)Memory used [KB]: 10746
% 1.57/0.59  % (2486)Time elapsed: 0.170 s
% 1.57/0.59  % (2486)------------------------------
% 1.57/0.59  % (2486)------------------------------
% 1.57/0.59  % (2478)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (2478)Memory used [KB]: 10746
% 1.57/0.59  % (2478)Time elapsed: 0.161 s
% 1.57/0.59  % (2478)------------------------------
% 1.57/0.59  % (2478)------------------------------
% 2.30/0.68  % (2464)Refutation not found, incomplete strategy% (2464)------------------------------
% 2.30/0.68  % (2464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.69  % (2513)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.30/0.69  % (2511)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.30/0.69  % (2464)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.69  
% 2.30/0.69  % (2464)Memory used [KB]: 6268
% 2.30/0.69  % (2464)Time elapsed: 0.260 s
% 2.30/0.69  % (2464)------------------------------
% 2.30/0.69  % (2464)------------------------------
% 2.30/0.70  % (2513)Refutation not found, incomplete strategy% (2513)------------------------------
% 2.30/0.70  % (2513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.70  % (2513)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.70  
% 2.30/0.70  % (2513)Memory used [KB]: 6140
% 2.30/0.70  % (2513)Time elapsed: 0.071 s
% 2.30/0.70  % (2513)------------------------------
% 2.30/0.70  % (2513)------------------------------
% 2.30/0.70  % (2465)Refutation not found, incomplete strategy% (2465)------------------------------
% 2.30/0.70  % (2465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.70  % (2465)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.70  
% 2.30/0.70  % (2465)Memory used [KB]: 6268
% 2.30/0.70  % (2465)Time elapsed: 0.259 s
% 2.30/0.70  % (2465)------------------------------
% 2.30/0.70  % (2465)------------------------------
% 2.30/0.71  % (2512)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.70/0.74  % (2514)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.88/0.76  % (2514)Refutation not found, incomplete strategy% (2514)------------------------------
% 2.88/0.76  % (2514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.76  % (2514)Termination reason: Refutation not found, incomplete strategy
% 2.88/0.76  
% 2.88/0.76  % (2514)Memory used [KB]: 10746
% 2.88/0.76  % (2514)Time elapsed: 0.139 s
% 2.88/0.76  % (2514)------------------------------
% 2.88/0.76  % (2514)------------------------------
% 3.36/0.83  % (2516)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.36/0.84  % (2517)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.36/0.86  % (2515)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.36/0.87  % (2517)Refutation not found, incomplete strategy% (2517)------------------------------
% 3.36/0.87  % (2517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.87  % (2517)Termination reason: Refutation not found, incomplete strategy
% 3.36/0.87  
% 3.36/0.87  % (2517)Memory used [KB]: 10874
% 3.36/0.87  % (2517)Time elapsed: 0.134 s
% 3.36/0.87  % (2517)------------------------------
% 3.36/0.87  % (2517)------------------------------
% 3.68/0.88  % (2518)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.37/1.01  % (2468)Time limit reached!
% 4.37/1.01  % (2468)------------------------------
% 4.37/1.01  % (2468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/1.01  % (2468)Termination reason: Time limit
% 4.37/1.01  % (2468)Termination phase: Saturation
% 4.37/1.01  
% 4.37/1.01  % (2468)Memory used [KB]: 12792
% 4.37/1.01  % (2468)Time elapsed: 0.513 s
% 4.37/1.01  % (2468)------------------------------
% 4.37/1.01  % (2468)------------------------------
% 4.37/1.02  % (2519)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.74/1.04  % (2469)Time limit reached!
% 4.74/1.04  % (2469)------------------------------
% 4.74/1.04  % (2469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.04  % (2476)Time limit reached!
% 4.74/1.04  % (2476)------------------------------
% 4.74/1.04  % (2476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.04  % (2476)Termination reason: Time limit
% 4.74/1.04  
% 4.74/1.04  % (2476)Memory used [KB]: 3326
% 4.74/1.04  % (2476)Time elapsed: 0.540 s
% 4.74/1.04  % (2476)------------------------------
% 4.74/1.04  % (2476)------------------------------
% 4.74/1.04  % (2469)Termination reason: Time limit
% 4.74/1.04  
% 4.74/1.04  % (2469)Memory used [KB]: 4093
% 4.74/1.04  % (2469)Time elapsed: 0.613 s
% 4.74/1.04  % (2469)------------------------------
% 4.74/1.04  % (2469)------------------------------
% 6.02/1.14  % (2521)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.35/1.19  % (2520)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.35/1.23  % (2522)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 6.90/1.25  % (2463)Time limit reached!
% 6.90/1.25  % (2463)------------------------------
% 6.90/1.25  % (2463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.25  % (2463)Termination reason: Time limit
% 6.90/1.25  
% 6.90/1.25  % (2463)Memory used [KB]: 4861
% 6.90/1.25  % (2463)Time elapsed: 0.818 s
% 6.90/1.25  % (2463)------------------------------
% 6.90/1.25  % (2463)------------------------------
% 7.71/1.36  % (2523)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 7.71/1.42  % (2474)Time limit reached!
% 7.71/1.42  % (2474)------------------------------
% 7.71/1.42  % (2474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.71/1.42  % (2474)Termination reason: Time limit
% 7.71/1.42  % (2474)Termination phase: Saturation
% 7.71/1.42  
% 7.71/1.42  % (2474)Memory used [KB]: 13688
% 7.71/1.42  % (2474)Time elapsed: 1.0000 s
% 7.71/1.42  % (2474)------------------------------
% 7.71/1.42  % (2474)------------------------------
% 9.22/1.56  % (2524)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.38/1.61  % (2462)Time limit reached!
% 9.38/1.61  % (2462)------------------------------
% 9.38/1.61  % (2462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.38/1.61  % (2462)Termination reason: Time limit
% 9.38/1.61  % (2462)Termination phase: Saturation
% 9.38/1.61  
% 9.38/1.61  % (2462)Memory used [KB]: 6140
% 9.38/1.61  % (2462)Time elapsed: 1.200 s
% 9.38/1.61  % (2462)------------------------------
% 9.38/1.61  % (2462)------------------------------
% 10.25/1.70  % (2524)Refutation not found, incomplete strategy% (2524)------------------------------
% 10.25/1.70  % (2524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.70  % (2524)Termination reason: Refutation not found, incomplete strategy
% 10.25/1.70  
% 10.25/1.70  % (2524)Memory used [KB]: 11897
% 10.25/1.70  % (2524)Time elapsed: 0.260 s
% 10.25/1.70  % (2524)------------------------------
% 10.25/1.70  % (2524)------------------------------
% 10.86/1.76  % (2467)Time limit reached!
% 10.86/1.76  % (2467)------------------------------
% 10.86/1.76  % (2467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.86/1.76  % (2467)Termination reason: Time limit
% 10.86/1.76  
% 10.86/1.76  % (2467)Memory used [KB]: 7419
% 10.86/1.76  % (2467)Time elapsed: 1.348 s
% 10.86/1.76  % (2467)------------------------------
% 10.86/1.76  % (2467)------------------------------
% 10.86/1.77  % (2525)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.66/1.88  % (2526)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.66/1.88  % (2520)Time limit reached!
% 11.66/1.88  % (2520)------------------------------
% 11.66/1.88  % (2520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.88  % (2520)Termination reason: Time limit
% 11.66/1.88  
% 11.66/1.88  % (2520)Memory used [KB]: 13688
% 11.66/1.88  % (2520)Time elapsed: 0.816 s
% 11.66/1.88  % (2520)------------------------------
% 11.66/1.88  % (2520)------------------------------
% 11.66/1.91  % (2527)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 12.44/2.03  % (2488)Time limit reached!
% 12.44/2.03  % (2488)------------------------------
% 12.44/2.03  % (2488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.44/2.03  % (2488)Termination reason: Time limit
% 12.44/2.03  % (2488)Termination phase: Saturation
% 12.44/2.03  
% 12.44/2.03  % (2488)Memory used [KB]: 20084
% 12.44/2.03  % (2488)Time elapsed: 1.600 s
% 12.44/2.03  % (2488)------------------------------
% 12.44/2.03  % (2488)------------------------------
% 12.99/2.05  % (2528)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 14.20/2.20  % (2526)Time limit reached!
% 14.20/2.20  % (2526)------------------------------
% 14.20/2.20  % (2526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.20/2.20  % (2526)Termination reason: Time limit
% 14.20/2.20  % (2526)Termination phase: Saturation
% 14.20/2.20  
% 14.20/2.20  % (2526)Memory used [KB]: 7547
% 14.20/2.20  % (2526)Time elapsed: 0.400 s
% 14.20/2.20  % (2526)------------------------------
% 14.20/2.20  % (2526)------------------------------
% 14.20/2.21  % (2529)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 14.20/2.22  % (2482)Time limit reached!
% 14.20/2.22  % (2482)------------------------------
% 14.20/2.22  % (2482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.20/2.22  % (2482)Termination reason: Time limit
% 14.20/2.22  
% 14.20/2.22  % (2482)Memory used [KB]: 17142
% 14.20/2.22  % (2482)Time elapsed: 1.812 s
% 14.20/2.22  % (2482)------------------------------
% 14.20/2.22  % (2482)------------------------------
% 15.09/2.29  % (2527)Time limit reached!
% 15.09/2.29  % (2527)------------------------------
% 15.09/2.29  % (2527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.09/2.29  % (2527)Termination reason: Time limit
% 15.09/2.29  % (2527)Termination phase: Saturation
% 15.09/2.29  
% 15.09/2.29  % (2527)Memory used [KB]: 10490
% 15.09/2.29  % (2527)Time elapsed: 0.500 s
% 15.09/2.29  % (2527)------------------------------
% 15.09/2.29  % (2527)------------------------------
% 15.09/2.31  % (2530)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 15.09/2.32  % (2528)Time limit reached!
% 15.09/2.32  % (2528)------------------------------
% 15.09/2.32  % (2528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.09/2.34  % (2528)Termination reason: Time limit
% 15.09/2.34  % (2528)Termination phase: Saturation
% 15.09/2.34  
% 15.09/2.34  % (2528)Memory used [KB]: 7291
% 15.09/2.34  % (2528)Time elapsed: 0.400 s
% 15.09/2.34  % (2528)------------------------------
% 15.09/2.34  % (2528)------------------------------
% 15.59/2.36  % (2531)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.73/2.66  % (2531)Time limit reached!
% 17.73/2.66  % (2531)------------------------------
% 17.73/2.66  % (2531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.73/2.66  % (2531)Termination reason: Time limit
% 17.73/2.66  % (2531)Termination phase: Saturation
% 17.73/2.66  
% 17.73/2.66  % (2531)Memory used [KB]: 7803
% 17.73/2.66  % (2531)Time elapsed: 0.400 s
% 17.73/2.66  % (2531)------------------------------
% 17.73/2.66  % (2531)------------------------------
% 18.08/2.69  % (2530)Time limit reached!
% 18.08/2.69  % (2530)------------------------------
% 18.08/2.69  % (2530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.08/2.69  % (2530)Termination reason: Time limit
% 18.08/2.69  
% 18.08/2.69  % (2530)Memory used [KB]: 4093
% 18.08/2.69  % (2530)Time elapsed: 0.410 s
% 18.08/2.69  % (2530)------------------------------
% 18.08/2.69  % (2530)------------------------------
% 19.02/2.83  % (2483)Refutation found. Thanks to Tanya!
% 19.02/2.83  % SZS status Theorem for theBenchmark
% 19.64/2.84  % SZS output start Proof for theBenchmark
% 19.64/2.84  fof(f21199,plain,(
% 19.64/2.84    $false),
% 19.64/2.84    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f146,f151,f370,f373,f629,f722,f770,f774,f1827,f1889,f4784,f4843,f4856,f5154,f5354,f5362,f5400,f14167,f14189,f16703,f16758,f16771,f16781,f20077,f20189,f21198])).
% 19.64/2.84  fof(f21198,plain,(
% 19.64/2.84    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_25 | spl7_45 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245),
% 19.64/2.84    inference(avatar_contradiction_clause,[],[f21197])).
% 19.64/2.84  fof(f21197,plain,(
% 19.64/2.84    $false | (spl7_1 | ~spl7_2 | ~spl7_4 | spl7_25 | spl7_45 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(subsumption_resolution,[],[f21196,f125])).
% 19.64/2.84  fof(f125,plain,(
% 19.64/2.84    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) | spl7_1),
% 19.64/2.84    inference(avatar_component_clause,[],[f123])).
% 19.64/2.84  fof(f123,plain,(
% 19.64/2.84    spl7_1 <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 19.64/2.84  fof(f21196,plain,(
% 19.64/2.84    k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | (~spl7_2 | ~spl7_4 | spl7_25 | spl7_45 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(equality_resolution,[],[f21188])).
% 19.64/2.84  fof(f21188,plain,(
% 19.64/2.84    ( ! [X21] : (sK3 != X21 | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21)) ) | (~spl7_2 | ~spl7_4 | spl7_25 | spl7_45 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(subsumption_resolution,[],[f21164,f609])).
% 19.64/2.84  fof(f609,plain,(
% 19.64/2.84    k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2) | spl7_45),
% 19.64/2.84    inference(avatar_component_clause,[],[f608])).
% 19.64/2.84  fof(f608,plain,(
% 19.64/2.84    spl7_45 <=> k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 19.64/2.84  fof(f21164,plain,(
% 19.64/2.84    ( ! [X21] : (sK3 != X21 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21)) ) | (~spl7_2 | ~spl7_4 | spl7_25 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(duplicate_literal_removal,[],[f21161])).
% 19.64/2.84  fof(f21161,plain,(
% 19.64/2.84    ( ! [X21] : (sK3 != X21 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X21)) ) | (~spl7_2 | ~spl7_4 | spl7_25 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(superposition,[],[f81,f20450])).
% 19.64/2.84  fof(f20450,plain,(
% 19.64/2.84    ( ! [X2] : (sK3 = sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)) ) | (~spl7_2 | ~spl7_4 | spl7_25 | ~spl7_46 | ~spl7_59 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(subsumption_resolution,[],[f20449,f6266])).
% 19.64/2.84  fof(f6266,plain,(
% 19.64/2.84    ( ! [X24] : (v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24)) ) | (spl7_25 | ~spl7_46 | ~spl7_59 | ~spl7_61)),
% 19.64/2.84    inference(subsumption_resolution,[],[f6265,f786])).
% 19.64/2.84  fof(f786,plain,(
% 19.64/2.84    ( ! [X2] : (v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1)) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)) ) | ~spl7_59),
% 19.64/2.84    inference(avatar_component_clause,[],[f785])).
% 19.64/2.84  fof(f785,plain,(
% 19.64/2.84    spl7_59 <=> ! [X2] : (v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1)) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 19.64/2.84  fof(f6265,plain,(
% 19.64/2.84    ( ! [X24] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24) | v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0) | ~v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0,k1_tarski(sK1))) ) | (spl7_25 | ~spl7_46 | ~spl7_61)),
% 19.64/2.84    inference(subsumption_resolution,[],[f6264,f613])).
% 19.64/2.84  fof(f613,plain,(
% 19.64/2.84    ( ! [X0] : (v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | ~spl7_46),
% 19.64/2.84    inference(avatar_component_clause,[],[f612])).
% 19.64/2.84  fof(f612,plain,(
% 19.64/2.84    spl7_46 <=> ! [X0] : (v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 19.64/2.84  fof(f6264,plain,(
% 19.64/2.84    ( ! [X24] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24) | v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0) | ~v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24))) ) | (spl7_25 | ~spl7_61)),
% 19.64/2.84    inference(subsumption_resolution,[],[f6234,f312])).
% 19.64/2.84  fof(f312,plain,(
% 19.64/2.84    k1_xboole_0 != k1_tarski(sK1) | spl7_25),
% 19.64/2.84    inference(avatar_component_clause,[],[f311])).
% 19.64/2.84  fof(f311,plain,(
% 19.64/2.84    spl7_25 <=> k1_xboole_0 = k1_tarski(sK1)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 19.64/2.84  fof(f6234,plain,(
% 19.64/2.84    ( ! [X24] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X24) | k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0) | ~v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X24))) ) | ~spl7_61),
% 19.64/2.84    inference(resolution,[],[f826,f120])).
% 19.64/2.84  fof(f120,plain,(
% 19.64/2.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(duplicate_literal_removal,[],[f94])).
% 19.64/2.84  fof(f94,plain,(
% 19.64/2.84    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f33])).
% 19.64/2.84  fof(f33,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.64/2.84    inference(flattening,[],[f32])).
% 19.64/2.84  fof(f32,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.64/2.84    inference(ennf_transformation,[],[f13])).
% 19.64/2.84  fof(f13,axiom,(
% 19.64/2.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 19.64/2.84  fof(f826,plain,(
% 19.64/2.84    ( ! [X2] : (m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)) ) | ~spl7_61),
% 19.64/2.84    inference(avatar_component_clause,[],[f825])).
% 19.64/2.84  fof(f825,plain,(
% 19.64/2.84    spl7_61 <=> ! [X2] : (m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 19.64/2.84  fof(f20449,plain,(
% 19.64/2.84    ( ! [X2] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) | sK3 = sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2) | ~v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0)) ) | (~spl7_2 | ~spl7_4 | ~spl7_46 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(subsumption_resolution,[],[f20419,f613])).
% 19.64/2.84  fof(f20419,plain,(
% 19.64/2.84    ( ! [X2] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) | ~v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)) | sK3 = sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2) | ~v1_partfun1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0)) ) | (~spl7_2 | ~spl7_4 | ~spl7_61 | ~spl7_245)),
% 19.64/2.84    inference(resolution,[],[f826,f7899])).
% 19.64/2.84  fof(f7899,plain,(
% 19.64/2.84    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0) | sK3 = X0 | ~v1_partfun1(X0,sK0)) ) | (~spl7_2 | ~spl7_4 | ~spl7_245)),
% 19.64/2.84    inference(subsumption_resolution,[],[f5379,f532])).
% 19.64/2.84  fof(f532,plain,(
% 19.64/2.84    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(X0,sK3) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_4)),
% 19.64/2.84    inference(subsumption_resolution,[],[f524,f140])).
% 19.64/2.84  fof(f140,plain,(
% 19.64/2.84    v1_funct_1(sK3) | ~spl7_4),
% 19.64/2.84    inference(avatar_component_clause,[],[f138])).
% 19.64/2.84  fof(f138,plain,(
% 19.64/2.84    spl7_4 <=> v1_funct_1(sK3)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 19.64/2.84  fof(f524,plain,(
% 19.64/2.84    ( ! [X0] : (r1_partfun1(X0,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | ~spl7_2),
% 19.64/2.84    inference(resolution,[],[f97,f130])).
% 19.64/2.84  fof(f130,plain,(
% 19.64/2.84    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_2),
% 19.64/2.84    inference(avatar_component_clause,[],[f128])).
% 19.64/2.84  fof(f128,plain,(
% 19.64/2.84    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 19.64/2.84  fof(f97,plain,(
% 19.64/2.84    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f37])).
% 19.64/2.84  fof(f37,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 19.64/2.84    inference(flattening,[],[f36])).
% 19.64/2.84  fof(f36,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 19.64/2.84    inference(ennf_transformation,[],[f14])).
% 19.64/2.84  fof(f14,axiom,(
% 19.64/2.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 19.64/2.84  fof(f5379,plain,(
% 19.64/2.84    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | sK3 = X0 | ~v1_partfun1(X0,sK0)) ) | ~spl7_245),
% 19.64/2.84    inference(avatar_component_clause,[],[f5378])).
% 19.64/2.84  fof(f5378,plain,(
% 19.64/2.84    spl7_245 <=> ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | sK3 = X0 | ~v1_partfun1(X0,sK0))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_245])])).
% 19.64/2.84  fof(f81,plain,(
% 19.64/2.84    ( ! [X0,X1] : (sK6(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 19.64/2.84    inference(cnf_transformation,[],[f52])).
% 19.64/2.84  fof(f52,plain,(
% 19.64/2.84    ! [X0,X1] : ((sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 19.64/2.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f51])).
% 19.64/2.84  fof(f51,plain,(
% 19.64/2.84    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)))),
% 19.64/2.84    introduced(choice_axiom,[])).
% 19.64/2.84  fof(f28,plain,(
% 19.64/2.84    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 19.64/2.84    inference(ennf_transformation,[],[f6])).
% 19.64/2.84  fof(f6,axiom,(
% 19.64/2.84    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 19.64/2.84  fof(f20189,plain,(
% 19.64/2.84    spl7_61 | ~spl7_5 | ~spl7_6 | spl7_45),
% 19.64/2.84    inference(avatar_split_clause,[],[f20188,f608,f148,f143,f825])).
% 19.64/2.84  fof(f143,plain,(
% 19.64/2.84    spl7_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 19.64/2.84  fof(f148,plain,(
% 19.64/2.84    spl7_6 <=> v1_funct_1(sK2)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 19.64/2.84  fof(f20188,plain,(
% 19.64/2.84    ( ! [X4] : (m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X4),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X4)) ) | (~spl7_5 | ~spl7_6 | spl7_45)),
% 19.64/2.84    inference(subsumption_resolution,[],[f20186,f609])).
% 19.64/2.84  fof(f20186,plain,(
% 19.64/2.84    ( ! [X4] : (m1_subset_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X4),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X4)) ) | (~spl7_5 | ~spl7_6)),
% 19.64/2.84    inference(resolution,[],[f518,f80])).
% 19.64/2.84  fof(f80,plain,(
% 19.64/2.84    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 19.64/2.84    inference(cnf_transformation,[],[f52])).
% 19.64/2.84  fof(f518,plain,(
% 19.64/2.84    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) ) | (~spl7_5 | ~spl7_6)),
% 19.64/2.84    inference(subsumption_resolution,[],[f510,f150])).
% 19.64/2.84  fof(f150,plain,(
% 19.64/2.84    v1_funct_1(sK2) | ~spl7_6),
% 19.64/2.84    inference(avatar_component_clause,[],[f148])).
% 19.64/2.84  fof(f510,plain,(
% 19.64/2.84    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK2)) ) | ~spl7_5),
% 19.64/2.84    inference(resolution,[],[f93,f145])).
% 19.64/2.84  fof(f145,plain,(
% 19.64/2.84    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_5),
% 19.64/2.84    inference(avatar_component_clause,[],[f143])).
% 19.64/2.84  fof(f93,plain,(
% 19.64/2.84    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f31])).
% 19.64/2.84  fof(f31,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.64/2.84    inference(flattening,[],[f30])).
% 19.64/2.84  fof(f30,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.64/2.84    inference(ennf_transformation,[],[f18])).
% 19.64/2.84  fof(f18,axiom,(
% 19.64/2.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 19.64/2.84  fof(f20077,plain,(
% 19.64/2.84    spl7_245 | ~spl7_2 | ~spl7_4 | ~spl7_34),
% 19.64/2.84    inference(avatar_split_clause,[],[f20076,f471,f138,f128,f5378])).
% 19.64/2.84  fof(f471,plain,(
% 19.64/2.84    spl7_34 <=> v1_partfun1(sK3,sK0)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 19.64/2.84  fof(f20076,plain,(
% 19.64/2.84    ( ! [X10] : (~r1_partfun1(X10,sK3) | ~v1_partfun1(X10,sK0) | sK3 = X10 | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X10)) ) | (~spl7_2 | ~spl7_4 | ~spl7_34)),
% 19.64/2.84    inference(subsumption_resolution,[],[f20075,f140])).
% 19.64/2.84  fof(f20075,plain,(
% 19.64/2.84    ( ! [X10] : (~r1_partfun1(X10,sK3) | ~v1_partfun1(X10,sK0) | sK3 = X10 | ~v1_funct_1(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X10)) ) | (~spl7_2 | ~spl7_34)),
% 19.64/2.84    inference(subsumption_resolution,[],[f20030,f473])).
% 19.64/2.84  fof(f473,plain,(
% 19.64/2.84    v1_partfun1(sK3,sK0) | ~spl7_34),
% 19.64/2.84    inference(avatar_component_clause,[],[f471])).
% 19.64/2.84  fof(f20030,plain,(
% 19.64/2.84    ( ! [X10] : (~r1_partfun1(X10,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X10,sK0) | sK3 = X10 | ~v1_funct_1(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X10)) ) | ~spl7_2),
% 19.64/2.84    inference(resolution,[],[f130,f102])).
% 19.64/2.84  fof(f102,plain,(
% 19.64/2.84    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f40])).
% 19.64/2.84  fof(f40,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.64/2.84    inference(flattening,[],[f39])).
% 19.64/2.84  fof(f39,plain,(
% 19.64/2.84    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.64/2.84    inference(ennf_transformation,[],[f16])).
% 19.64/2.84  fof(f16,axiom,(
% 19.64/2.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 19.64/2.84  fof(f16781,plain,(
% 19.64/2.84    ~spl7_11 | spl7_12 | ~spl7_8),
% 19.64/2.84    inference(avatar_split_clause,[],[f16776,f163,f187,f183])).
% 19.64/2.84  fof(f183,plain,(
% 19.64/2.84    spl7_11 <=> r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 19.64/2.84  fof(f187,plain,(
% 19.64/2.84    spl7_12 <=> sK2 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 19.64/2.84  fof(f163,plain,(
% 19.64/2.84    spl7_8 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1)))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 19.64/2.84  fof(f16776,plain,(
% 19.64/2.84    sK2 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) | ~spl7_8),
% 19.64/2.84    inference(resolution,[],[f165,f87])).
% 19.64/2.84  fof(f87,plain,(
% 19.64/2.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f56])).
% 19.64/2.84  fof(f56,plain,(
% 19.64/2.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.64/2.84    inference(flattening,[],[f55])).
% 19.64/2.84  fof(f55,plain,(
% 19.64/2.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.64/2.84    inference(nnf_transformation,[],[f1])).
% 19.64/2.84  fof(f1,axiom,(
% 19.64/2.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 19.64/2.84  fof(f165,plain,(
% 19.64/2.84    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~spl7_8),
% 19.64/2.84    inference(avatar_component_clause,[],[f163])).
% 19.64/2.84  fof(f16771,plain,(
% 19.64/2.84    ~spl7_9 | spl7_10 | ~spl7_7),
% 19.64/2.84    inference(avatar_split_clause,[],[f16763,f158,f178,f174])).
% 19.64/2.84  fof(f174,plain,(
% 19.64/2.84    spl7_9 <=> r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 19.64/2.84  fof(f178,plain,(
% 19.64/2.84    spl7_10 <=> k2_zfmisc_1(sK0,k1_tarski(sK1)) = sK3),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 19.64/2.84  fof(f158,plain,(
% 19.64/2.84    spl7_7 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1)))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 19.64/2.84  fof(f16763,plain,(
% 19.64/2.84    k2_zfmisc_1(sK0,k1_tarski(sK1)) = sK3 | ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) | ~spl7_7),
% 19.64/2.84    inference(resolution,[],[f160,f87])).
% 19.64/2.84  fof(f160,plain,(
% 19.64/2.84    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~spl7_7),
% 19.64/2.84    inference(avatar_component_clause,[],[f158])).
% 19.64/2.84  fof(f16758,plain,(
% 19.64/2.84    spl7_8 | ~spl7_5),
% 19.64/2.84    inference(avatar_split_clause,[],[f16726,f143,f163])).
% 19.64/2.84  fof(f16726,plain,(
% 19.64/2.84    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~spl7_5),
% 19.64/2.84    inference(resolution,[],[f145,f98])).
% 19.64/2.84  fof(f98,plain,(
% 19.64/2.84    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f57])).
% 19.64/2.84  fof(f57,plain,(
% 19.64/2.84    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.64/2.84    inference(nnf_transformation,[],[f11])).
% 19.64/2.84  fof(f11,axiom,(
% 19.64/2.84    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.64/2.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 19.64/2.84  fof(f16703,plain,(
% 19.64/2.84    spl7_7 | ~spl7_2),
% 19.64/2.84    inference(avatar_split_clause,[],[f16650,f128,f158])).
% 19.64/2.84  fof(f16650,plain,(
% 19.64/2.84    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~spl7_2),
% 19.64/2.84    inference(resolution,[],[f130,f98])).
% 19.64/2.84  fof(f14189,plain,(
% 19.64/2.84    spl7_59 | ~spl7_5 | ~spl7_6 | spl7_45),
% 19.64/2.84    inference(avatar_split_clause,[],[f14188,f608,f148,f143,f785])).
% 19.64/2.84  fof(f14188,plain,(
% 19.64/2.84    ( ! [X2] : (v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1)) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)) ) | (~spl7_5 | ~spl7_6 | spl7_45)),
% 19.64/2.84    inference(subsumption_resolution,[],[f14186,f609])).
% 19.64/2.84  fof(f14186,plain,(
% 19.64/2.84    ( ! [X2] : (v1_funct_2(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0,k1_tarski(sK1)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)) ) | (~spl7_5 | ~spl7_6)),
% 19.64/2.84    inference(resolution,[],[f455,f80])).
% 19.64/2.84  fof(f455,plain,(
% 19.64/2.84    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X1,sK0,k1_tarski(sK1))) ) | (~spl7_5 | ~spl7_6)),
% 19.64/2.84    inference(subsumption_resolution,[],[f448,f150])).
% 19.64/2.84  fof(f448,plain,(
% 19.64/2.84    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2)) ) | ~spl7_5),
% 19.64/2.84    inference(resolution,[],[f92,f145])).
% 19.64/2.84  fof(f92,plain,(
% 19.64/2.84    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f31])).
% 19.64/2.84  fof(f14167,plain,(
% 19.64/2.84    spl7_45 | spl7_46 | ~spl7_5 | ~spl7_6),
% 19.64/2.84    inference(avatar_split_clause,[],[f14165,f148,f143,f612,f608])).
% 19.64/2.84  fof(f14165,plain,(
% 19.64/2.84    ( ! [X2] : (v1_funct_1(sK6(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2)) ) | (~spl7_5 | ~spl7_6)),
% 19.64/2.84    inference(resolution,[],[f337,f80])).
% 19.64/2.84  fof(f337,plain,(
% 19.64/2.84    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X1)) ) | (~spl7_5 | ~spl7_6)),
% 19.64/2.84    inference(subsumption_resolution,[],[f330,f150])).
% 19.64/2.84  fof(f330,plain,(
% 19.64/2.84    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | ~spl7_5),
% 19.64/2.84    inference(resolution,[],[f91,f145])).
% 19.64/2.84  fof(f91,plain,(
% 19.64/2.84    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f31])).
% 19.64/2.84  fof(f5400,plain,(
% 19.64/2.84    spl7_25 | ~spl7_3 | spl7_34 | ~spl7_4 | ~spl7_7),
% 19.64/2.84    inference(avatar_split_clause,[],[f5399,f158,f138,f471,f133,f311])).
% 19.64/2.84  fof(f133,plain,(
% 19.64/2.84    spl7_3 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 19.64/2.84  fof(f5399,plain,(
% 19.64/2.84    v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | (~spl7_4 | ~spl7_7)),
% 19.64/2.84    inference(subsumption_resolution,[],[f3240,f140])).
% 19.64/2.84  fof(f3240,plain,(
% 19.64/2.84    v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | k1_xboole_0 = k1_tarski(sK1) | ~spl7_7),
% 19.64/2.84    inference(resolution,[],[f160,f463])).
% 19.64/2.84  fof(f463,plain,(
% 19.64/2.84    ( ! [X4,X2,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X2)) | v1_partfun1(X3,X4) | ~v1_funct_2(X3,X4,X2) | ~v1_funct_1(X3) | k1_xboole_0 = X2) )),
% 19.64/2.84    inference(resolution,[],[f120,f99])).
% 19.64/2.84  fof(f99,plain,(
% 19.64/2.84    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.64/2.84    inference(cnf_transformation,[],[f57])).
% 19.64/2.84  fof(f5362,plain,(
% 19.64/2.84    k1_xboole_0 != sK1 | k1_xboole_0 != sK3 | sK2 != k2_zfmisc_1(sK0,k1_tarski(sK1)) | k2_zfmisc_1(sK0,k1_tarski(sK1)) != sK3 | r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(sK1,k1_xboole_0)),
% 19.64/2.84    introduced(theory_tautology_sat_conflict,[])).
% 19.64/2.84  fof(f5354,plain,(
% 19.64/2.84    spl7_244 | ~spl7_25),
% 19.64/2.84    inference(avatar_split_clause,[],[f5347,f311,f5351])).
% 19.64/2.84  fof(f5351,plain,(
% 19.64/2.84    spl7_244 <=> k1_xboole_0 = sK1),
% 19.64/2.84    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).
% 19.64/2.84  fof(f5347,plain,(
% 19.64/2.84    k1_xboole_0 = sK1 | ~spl7_25),
% 19.64/2.84    inference(resolution,[],[f5173,f169])).
% 19.64/2.84  fof(f169,plain,(
% 19.64/2.84    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 19.64/2.84    inference(resolution,[],[f87,f104])).
% 19.64/2.85  % (2477)Time limit reached!
% 19.64/2.85  % (2477)------------------------------
% 19.64/2.85  % (2477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.64/2.85  % (2477)Termination reason: Time limit
% 19.64/2.85  % (2477)Termination phase: Saturation
% 19.64/2.85  
% 19.64/2.85  % (2477)Memory used [KB]: 15095
% 19.64/2.85  % (2477)Time elapsed: 2.426 s
% 19.64/2.85  % (2477)------------------------------
% 19.64/2.85  % (2477)------------------------------
% 19.64/2.85  fof(f104,plain,(
% 19.64/2.85    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.64/2.85    inference(cnf_transformation,[],[f2])).
% 19.64/2.85  fof(f2,axiom,(
% 19.64/2.85    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 19.64/2.85  fof(f5173,plain,(
% 19.64/2.85    ( ! [X2] : (r1_tarski(sK1,X2)) ) | ~spl7_25),
% 19.64/2.85    inference(resolution,[],[f4853,f98])).
% 19.64/2.85  fof(f4853,plain,(
% 19.64/2.85    ( ! [X37] : (m1_subset_1(sK1,X37)) ) | ~spl7_25),
% 19.64/2.85    inference(subsumption_resolution,[],[f4776,f104])).
% 19.64/2.85  fof(f4776,plain,(
% 19.64/2.85    ( ! [X37] : (~r1_tarski(k1_xboole_0,X37) | m1_subset_1(sK1,X37)) ) | ~spl7_25),
% 19.64/2.85    inference(superposition,[],[f869,f313])).
% 19.64/2.85  fof(f313,plain,(
% 19.64/2.85    k1_xboole_0 = k1_tarski(sK1) | ~spl7_25),
% 19.64/2.85    inference(avatar_component_clause,[],[f311])).
% 19.64/2.85  fof(f869,plain,(
% 19.64/2.85    ( ! [X6,X7] : (~r1_tarski(k1_tarski(X6),X7) | m1_subset_1(X6,X7)) )),
% 19.64/2.85    inference(resolution,[],[f196,f152])).
% 19.64/2.85  fof(f152,plain,(
% 19.64/2.85    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 19.64/2.85    inference(superposition,[],[f108,f90])).
% 19.64/2.85  fof(f90,plain,(
% 19.64/2.85    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.64/2.85    inference(cnf_transformation,[],[f4])).
% 19.64/2.85  fof(f4,axiom,(
% 19.64/2.85    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 19.64/2.85  fof(f108,plain,(
% 19.64/2.85    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 19.64/2.85    inference(equality_resolution,[],[f107])).
% 19.64/2.85  fof(f107,plain,(
% 19.64/2.85    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 19.64/2.85    inference(equality_resolution,[],[f65])).
% 19.64/2.85  fof(f65,plain,(
% 19.64/2.85    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.64/2.85    inference(cnf_transformation,[],[f48])).
% 19.64/2.85  fof(f48,plain,(
% 19.64/2.85    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.64/2.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 19.64/2.85  fof(f47,plain,(
% 19.64/2.85    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 19.64/2.85    introduced(choice_axiom,[])).
% 19.64/2.85  fof(f46,plain,(
% 19.64/2.85    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.64/2.85    inference(rectify,[],[f45])).
% 19.64/2.85  fof(f45,plain,(
% 19.64/2.85    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.64/2.85    inference(flattening,[],[f44])).
% 19.64/2.85  fof(f44,plain,(
% 19.64/2.85    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.64/2.85    inference(nnf_transformation,[],[f3])).
% 19.64/2.85  fof(f3,axiom,(
% 19.64/2.85    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 19.64/2.85  fof(f196,plain,(
% 19.64/2.85    ( ! [X6,X4,X5] : (~r2_hidden(X4,X6) | m1_subset_1(X4,X5) | ~r1_tarski(X6,X5)) )),
% 19.64/2.85    inference(resolution,[],[f96,f99])).
% 19.64/2.85  fof(f96,plain,(
% 19.64/2.85    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 19.64/2.85    inference(cnf_transformation,[],[f35])).
% 19.64/2.85  fof(f35,plain,(
% 19.64/2.85    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.64/2.85    inference(flattening,[],[f34])).
% 19.64/2.85  fof(f34,plain,(
% 19.64/2.85    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 19.64/2.85    inference(ennf_transformation,[],[f12])).
% 19.64/2.85  fof(f12,axiom,(
% 19.64/2.85    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 19.64/2.85  fof(f5154,plain,(
% 19.64/2.85    spl7_62 | ~spl7_18),
% 19.64/2.85    inference(avatar_split_clause,[],[f5153,f260,f833])).
% 19.64/2.85  fof(f833,plain,(
% 19.64/2.85    spl7_62 <=> k1_xboole_0 = sK3),
% 19.64/2.85    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 19.64/2.85  fof(f260,plain,(
% 19.64/2.85    spl7_18 <=> r1_tarski(sK3,k1_xboole_0)),
% 19.64/2.85    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 19.64/2.85  fof(f5153,plain,(
% 19.64/2.85    k1_xboole_0 = sK3 | ~spl7_18),
% 19.64/2.85    inference(subsumption_resolution,[],[f5151,f104])).
% 19.64/2.85  fof(f5151,plain,(
% 19.64/2.85    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl7_18),
% 19.64/2.85    inference(resolution,[],[f262,f87])).
% 19.64/2.85  fof(f262,plain,(
% 19.64/2.85    r1_tarski(sK3,k1_xboole_0) | ~spl7_18),
% 19.64/2.85    inference(avatar_component_clause,[],[f260])).
% 19.64/2.85  fof(f4856,plain,(
% 19.64/2.85    spl7_13 | ~spl7_25),
% 19.64/2.85    inference(avatar_split_clause,[],[f4762,f311,f233])).
% 19.64/2.85  fof(f233,plain,(
% 19.64/2.85    spl7_13 <=> r2_hidden(sK1,k1_xboole_0)),
% 19.64/2.85    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 19.64/2.85  fof(f4762,plain,(
% 19.64/2.85    r2_hidden(sK1,k1_xboole_0) | ~spl7_25),
% 19.64/2.85    inference(superposition,[],[f152,f313])).
% 19.64/2.85  fof(f4843,plain,(
% 19.64/2.85    spl7_23 | ~spl7_25),
% 19.64/2.85    inference(avatar_split_clause,[],[f4842,f311,f291])).
% 19.64/2.85  fof(f291,plain,(
% 19.64/2.85    spl7_23 <=> ! [X3] : k1_xboole_0 = X3),
% 19.64/2.85    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 19.64/2.85  fof(f4842,plain,(
% 19.64/2.85    ( ! [X1] : (k1_xboole_0 = X1) ) | ~spl7_25),
% 19.64/2.85    inference(subsumption_resolution,[],[f4759,f115])).
% 19.64/2.85  fof(f115,plain,(
% 19.64/2.85    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.64/2.85    inference(equality_resolution,[],[f84])).
% 19.64/2.85  fof(f84,plain,(
% 19.64/2.85    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.64/2.85    inference(cnf_transformation,[],[f54])).
% 19.64/2.85  fof(f54,plain,(
% 19.64/2.85    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.64/2.85    inference(flattening,[],[f53])).
% 19.64/2.85  fof(f53,plain,(
% 19.64/2.85    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.64/2.85    inference(nnf_transformation,[],[f7])).
% 19.64/2.85  fof(f7,axiom,(
% 19.64/2.85    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 19.64/2.85  fof(f4759,plain,(
% 19.64/2.85    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl7_25),
% 19.64/2.85    inference(superposition,[],[f89,f313])).
% 19.64/2.85  fof(f89,plain,(
% 19.64/2.85    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = X0) )),
% 19.64/2.85    inference(cnf_transformation,[],[f29])).
% 19.64/2.85  fof(f29,plain,(
% 19.64/2.85    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 19.64/2.85    inference(ennf_transformation,[],[f8])).
% 19.64/2.85  fof(f8,axiom,(
% 19.64/2.85    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 19.64/2.85  fof(f4784,plain,(
% 19.64/2.85    spl7_18 | ~spl7_7 | ~spl7_25),
% 19.64/2.85    inference(avatar_split_clause,[],[f4783,f311,f158,f260])).
% 19.64/2.85  fof(f4783,plain,(
% 19.64/2.85    r1_tarski(sK3,k1_xboole_0) | (~spl7_7 | ~spl7_25)),
% 19.64/2.85    inference(forward_demodulation,[],[f4729,f115])).
% 19.64/2.85  fof(f4729,plain,(
% 19.64/2.85    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl7_7 | ~spl7_25)),
% 19.64/2.85    inference(backward_demodulation,[],[f160,f313])).
% 19.64/2.85  fof(f1889,plain,(
% 19.64/2.85    ~spl7_23 | spl7_25),
% 19.64/2.85    inference(avatar_contradiction_clause,[],[f1888])).
% 19.64/2.85  fof(f1888,plain,(
% 19.64/2.85    $false | (~spl7_23 | spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f1748,f292])).
% 19.64/2.85  fof(f292,plain,(
% 19.64/2.85    ( ! [X3] : (k1_xboole_0 = X3) ) | ~spl7_23),
% 19.64/2.85    inference(avatar_component_clause,[],[f291])).
% 19.64/2.85  fof(f1748,plain,(
% 19.64/2.85    k1_xboole_0 != k1_tarski(k1_xboole_0) | (~spl7_23 | spl7_25)),
% 19.64/2.85    inference(backward_demodulation,[],[f312,f292])).
% 19.64/2.85  fof(f1827,plain,(
% 19.64/2.85    ~spl7_23 | spl7_45),
% 19.64/2.85    inference(avatar_contradiction_clause,[],[f1826])).
% 19.64/2.85  fof(f1826,plain,(
% 19.64/2.85    $false | (~spl7_23 | spl7_45)),
% 19.64/2.85    inference(subsumption_resolution,[],[f1704,f292])).
% 19.64/2.85  fof(f1704,plain,(
% 19.64/2.85    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,sK2) | (~spl7_23 | spl7_45)),
% 19.64/2.85    inference(backward_demodulation,[],[f609,f292])).
% 19.64/2.85  fof(f774,plain,(
% 19.64/2.85    spl7_23 | ~spl7_47),
% 19.64/2.85    inference(avatar_split_clause,[],[f773,f619,f291])).
% 19.64/2.85  fof(f619,plain,(
% 19.64/2.85    spl7_47 <=> k1_xboole_0 = k1_tarski(sK3)),
% 19.64/2.85    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 19.64/2.85  fof(f773,plain,(
% 19.64/2.85    ( ! [X1] : (k1_xboole_0 = X1) ) | ~spl7_47),
% 19.64/2.85    inference(subsumption_resolution,[],[f764,f115])).
% 19.64/2.85  fof(f764,plain,(
% 19.64/2.85    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl7_47),
% 19.64/2.85    inference(superposition,[],[f89,f620])).
% 19.64/2.85  fof(f620,plain,(
% 19.64/2.85    k1_xboole_0 = k1_tarski(sK3) | ~spl7_47),
% 19.64/2.85    inference(avatar_component_clause,[],[f619])).
% 19.64/2.85  fof(f770,plain,(
% 19.64/2.85    ~spl7_45 | spl7_1 | ~spl7_47),
% 19.64/2.85    inference(avatar_split_clause,[],[f762,f619,f123,f608])).
% 19.64/2.85  fof(f762,plain,(
% 19.64/2.85    k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2) | (spl7_1 | ~spl7_47)),
% 19.64/2.85    inference(backward_demodulation,[],[f125,f620])).
% 19.64/2.85  fof(f722,plain,(
% 19.64/2.85    ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_25 | ~spl7_45 | spl7_48),
% 19.64/2.85    inference(avatar_contradiction_clause,[],[f721])).
% 19.64/2.85  fof(f721,plain,(
% 19.64/2.85    $false | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_25 | ~spl7_45 | spl7_48)),
% 19.64/2.85    inference(subsumption_resolution,[],[f720,f628])).
% 19.64/2.85  fof(f628,plain,(
% 19.64/2.85    ~r2_hidden(sK3,k1_xboole_0) | spl7_48),
% 19.64/2.85    inference(avatar_component_clause,[],[f626])).
% 19.64/2.85  fof(f626,plain,(
% 19.64/2.85    spl7_48 <=> r2_hidden(sK3,k1_xboole_0)),
% 19.64/2.85    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 19.64/2.85  fof(f720,plain,(
% 19.64/2.85    r2_hidden(sK3,k1_xboole_0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_25 | ~spl7_45)),
% 19.64/2.85    inference(forward_demodulation,[],[f719,f610])).
% 19.64/2.85  fof(f610,plain,(
% 19.64/2.85    k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~spl7_45),
% 19.64/2.85    inference(avatar_component_clause,[],[f608])).
% 19.64/2.85  fof(f719,plain,(
% 19.64/2.85    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f709,f150])).
% 19.64/2.85  fof(f709,plain,(
% 19.64/2.85    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | ~v1_funct_1(sK2) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_25)),
% 19.64/2.85    inference(resolution,[],[f692,f145])).
% 19.64/2.85  fof(f692,plain,(
% 19.64/2.85    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f584,f532])).
% 19.64/2.85  fof(f584,plain,(
% 19.64/2.85    ( ! [X0] : (~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f583,f140])).
% 19.64/2.85  fof(f583,plain,(
% 19.64/2.85    ( ! [X0] : (~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_3 | spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f582,f135])).
% 19.64/2.85  fof(f135,plain,(
% 19.64/2.85    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl7_3),
% 19.64/2.85    inference(avatar_component_clause,[],[f133])).
% 19.64/2.85  fof(f582,plain,(
% 19.64/2.85    ( ! [X0] : (~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl7_2 | spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f573,f312])).
% 19.64/2.85  fof(f573,plain,(
% 19.64/2.85    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | ~spl7_2),
% 19.64/2.85    inference(resolution,[],[f70,f130])).
% 19.64/2.85  fof(f70,plain,(
% 19.64/2.85    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.64/2.85    inference(cnf_transformation,[],[f25])).
% 19.64/2.85  fof(f25,plain,(
% 19.64/2.85    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.64/2.85    inference(flattening,[],[f24])).
% 19.64/2.85  fof(f24,plain,(
% 19.64/2.85    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.64/2.85    inference(ennf_transformation,[],[f17])).
% 19.64/2.85  fof(f17,axiom,(
% 19.64/2.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 19.64/2.85  fof(f629,plain,(
% 19.64/2.85    ~spl7_48 | spl7_47),
% 19.64/2.85    inference(avatar_split_clause,[],[f624,f619,f626])).
% 19.64/2.85  fof(f624,plain,(
% 19.64/2.85    ~r2_hidden(sK3,k1_xboole_0) | spl7_47),
% 19.64/2.85    inference(trivial_inequality_removal,[],[f623])).
% 19.64/2.85  fof(f623,plain,(
% 19.64/2.85    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK3,k1_xboole_0) | spl7_47),
% 19.64/2.85    inference(superposition,[],[f621,f211])).
% 19.64/2.85  fof(f211,plain,(
% 19.64/2.85    ( ! [X2] : (k1_xboole_0 = k1_tarski(X2) | ~r2_hidden(X2,k1_xboole_0)) )),
% 19.64/2.85    inference(resolution,[],[f168,f169])).
% 19.64/2.85  fof(f168,plain,(
% 19.64/2.85    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.64/2.85    inference(resolution,[],[f100,f98])).
% 19.64/2.85  fof(f100,plain,(
% 19.64/2.85    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 19.64/2.85    inference(cnf_transformation,[],[f38])).
% 19.64/2.85  fof(f38,plain,(
% 19.64/2.85    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 19.64/2.85    inference(ennf_transformation,[],[f10])).
% 19.64/2.85  fof(f10,axiom,(
% 19.64/2.85    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 19.64/2.85  fof(f621,plain,(
% 19.64/2.85    k1_xboole_0 != k1_tarski(sK3) | spl7_47),
% 19.64/2.85    inference(avatar_component_clause,[],[f619])).
% 19.64/2.85  fof(f373,plain,(
% 19.64/2.85    spl7_11 | ~spl7_25),
% 19.64/2.85    inference(avatar_contradiction_clause,[],[f372])).
% 19.64/2.85  fof(f372,plain,(
% 19.64/2.85    $false | (spl7_11 | ~spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f371,f104])).
% 19.64/2.85  fof(f371,plain,(
% 19.64/2.85    ~r1_tarski(k1_xboole_0,sK2) | (spl7_11 | ~spl7_25)),
% 19.64/2.85    inference(forward_demodulation,[],[f349,f115])).
% 19.64/2.85  fof(f349,plain,(
% 19.64/2.85    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | (spl7_11 | ~spl7_25)),
% 19.64/2.85    inference(backward_demodulation,[],[f185,f313])).
% 19.64/2.85  fof(f185,plain,(
% 19.64/2.85    ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) | spl7_11),
% 19.64/2.85    inference(avatar_component_clause,[],[f183])).
% 19.64/2.85  fof(f370,plain,(
% 19.64/2.85    spl7_9 | ~spl7_25),
% 19.64/2.85    inference(avatar_contradiction_clause,[],[f369])).
% 19.64/2.85  fof(f369,plain,(
% 19.64/2.85    $false | (spl7_9 | ~spl7_25)),
% 19.64/2.85    inference(subsumption_resolution,[],[f368,f104])).
% 19.64/2.85  fof(f368,plain,(
% 19.64/2.85    ~r1_tarski(k1_xboole_0,sK3) | (spl7_9 | ~spl7_25)),
% 19.64/2.85    inference(forward_demodulation,[],[f348,f115])).
% 19.64/2.85  fof(f348,plain,(
% 19.64/2.85    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (spl7_9 | ~spl7_25)),
% 19.64/2.85    inference(backward_demodulation,[],[f176,f313])).
% 19.64/2.85  fof(f176,plain,(
% 19.64/2.85    ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) | spl7_9),
% 19.64/2.85    inference(avatar_component_clause,[],[f174])).
% 19.64/2.85  fof(f151,plain,(
% 19.64/2.85    spl7_6),
% 19.64/2.85    inference(avatar_split_clause,[],[f58,f148])).
% 19.64/2.85  fof(f58,plain,(
% 19.64/2.85    v1_funct_1(sK2)),
% 19.64/2.85    inference(cnf_transformation,[],[f43])).
% 19.64/2.85  fof(f43,plain,(
% 19.64/2.85    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 19.64/2.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f42,f41])).
% 19.64/2.85  fof(f41,plain,(
% 19.64/2.85    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 19.64/2.85    introduced(choice_axiom,[])).
% 19.64/2.85  fof(f42,plain,(
% 19.64/2.85    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 19.64/2.85    introduced(choice_axiom,[])).
% 19.64/2.85  fof(f23,plain,(
% 19.64/2.85    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 19.64/2.85    inference(flattening,[],[f22])).
% 19.64/2.85  fof(f22,plain,(
% 19.64/2.85    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 19.64/2.85    inference(ennf_transformation,[],[f21])).
% 19.64/2.85  fof(f21,negated_conjecture,(
% 19.64/2.85    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 19.64/2.85    inference(negated_conjecture,[],[f20])).
% 19.64/2.85  fof(f20,conjecture,(
% 19.64/2.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 19.64/2.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 19.64/2.85  fof(f146,plain,(
% 19.64/2.85    spl7_5),
% 19.64/2.85    inference(avatar_split_clause,[],[f59,f143])).
% 19.64/2.85  fof(f59,plain,(
% 19.64/2.85    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 19.64/2.85    inference(cnf_transformation,[],[f43])).
% 19.64/2.85  fof(f141,plain,(
% 19.64/2.85    spl7_4),
% 19.64/2.85    inference(avatar_split_clause,[],[f60,f138])).
% 19.64/2.85  fof(f60,plain,(
% 19.64/2.85    v1_funct_1(sK3)),
% 19.64/2.85    inference(cnf_transformation,[],[f43])).
% 19.64/2.85  fof(f136,plain,(
% 19.64/2.85    spl7_3),
% 19.64/2.85    inference(avatar_split_clause,[],[f61,f133])).
% 19.64/2.85  fof(f61,plain,(
% 19.64/2.85    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 19.64/2.85    inference(cnf_transformation,[],[f43])).
% 19.64/2.85  fof(f131,plain,(
% 19.64/2.85    spl7_2),
% 19.64/2.85    inference(avatar_split_clause,[],[f62,f128])).
% 19.64/2.85  fof(f62,plain,(
% 19.64/2.85    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 19.64/2.85    inference(cnf_transformation,[],[f43])).
% 19.64/2.85  fof(f126,plain,(
% 19.64/2.85    ~spl7_1),
% 19.64/2.85    inference(avatar_split_clause,[],[f63,f123])).
% 19.64/2.85  fof(f63,plain,(
% 19.64/2.85    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 19.64/2.85    inference(cnf_transformation,[],[f43])).
% 19.64/2.85  % SZS output end Proof for theBenchmark
% 19.64/2.85  % (2483)------------------------------
% 19.64/2.85  % (2483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.64/2.85  % (2483)Termination reason: Refutation
% 19.64/2.85  
% 19.64/2.85  % (2483)Memory used [KB]: 17782
% 19.64/2.85  % (2483)Time elapsed: 2.422 s
% 19.64/2.85  % (2483)------------------------------
% 19.64/2.85  % (2483)------------------------------
% 19.64/2.85  % (2459)Success in time 2.47 s
%------------------------------------------------------------------------------
