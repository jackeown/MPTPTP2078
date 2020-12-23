%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0971+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 22.11s
% Output     : Refutation 22.11s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 258 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  325 (1230 expanded)
%              Number of equality atoms :   41 ( 179 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19115,f13338])).

fof(f13338,plain,(
    r2_hidden(sK67(sK29,sK32,sK31),sK29) ),
    inference(subsumption_resolution,[],[f13337,f4420])).

fof(f4420,plain,(
    ~ v1_xboole_0(sK30) ),
    inference(subsumption_resolution,[],[f4413,f3749])).

fof(f3749,plain,(
    ~ v1_xboole_0(k2_relat_1(sK32)) ),
    inference(forward_demodulation,[],[f3608,f3472])).

fof(f3472,plain,(
    k2_relset_1(sK29,sK30,sK32) = k2_relat_1(sK32) ),
    inference(resolution,[],[f2402,f2523])).

fof(f2523,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1564])).

fof(f1564,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2402,plain,(
    m1_subset_1(sK32,k1_zfmisc_1(k2_zfmisc_1(sK29,sK30))) ),
    inference(cnf_transformation,[],[f2038])).

fof(f2038,plain,
    ( ! [X4] :
        ( sK31 != k1_funct_1(sK32,X4)
        | ~ r2_hidden(X4,sK29) )
    & r2_hidden(sK31,k2_relset_1(sK29,sK30,sK32))
    & m1_subset_1(sK32,k1_zfmisc_1(k2_zfmisc_1(sK29,sK30)))
    & v1_funct_2(sK32,sK29,sK30)
    & v1_funct_1(sK32) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29,sK30,sK31,sK32])],[f1502,f2037])).

fof(f2037,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK31 != k1_funct_1(sK32,X4)
          | ~ r2_hidden(X4,sK29) )
      & r2_hidden(sK31,k2_relset_1(sK29,sK30,sK32))
      & m1_subset_1(sK32,k1_zfmisc_1(k2_zfmisc_1(sK29,sK30)))
      & v1_funct_2(sK32,sK29,sK30)
      & v1_funct_1(sK32) ) ),
    introduced(choice_axiom,[])).

fof(f1502,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1501])).

fof(f1501,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1483])).

fof(f1483,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f1482])).

fof(f1482,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f3608,plain,(
    ~ v1_xboole_0(k2_relset_1(sK29,sK30,sK32)) ),
    inference(resolution,[],[f2403,f2933])).

fof(f2933,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1814])).

fof(f1814,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2403,plain,(
    r2_hidden(sK31,k2_relset_1(sK29,sK30,sK32)) ),
    inference(cnf_transformation,[],[f2038])).

fof(f4413,plain,
    ( ~ v1_xboole_0(sK30)
    | v1_xboole_0(k2_relat_1(sK32)) ),
    inference(resolution,[],[f3486,f2956])).

fof(f2956,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1833])).

fof(f1833,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f681])).

fof(f681,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f3486,plain,
    ( v1_xboole_0(sK32)
    | ~ v1_xboole_0(sK30) ),
    inference(resolution,[],[f2402,f2937])).

fof(f2937,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1820])).

fof(f1820,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f1213,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f13337,plain,
    ( v1_xboole_0(sK30)
    | r2_hidden(sK67(sK29,sK32,sK31),sK29) ),
    inference(subsumption_resolution,[],[f13336,f4450])).

fof(f4450,plain,(
    ~ v1_xboole_0(sK29) ),
    inference(subsumption_resolution,[],[f4443,f3749])).

fof(f4443,plain,
    ( ~ v1_xboole_0(sK29)
    | v1_xboole_0(k2_relat_1(sK32)) ),
    inference(resolution,[],[f3487,f2956])).

fof(f3487,plain,
    ( v1_xboole_0(sK32)
    | ~ v1_xboole_0(sK29) ),
    inference(resolution,[],[f2402,f2938])).

fof(f2938,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1821])).

fof(f1821,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1212])).

fof(f1212,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f13336,plain,
    ( v1_xboole_0(sK29)
    | v1_xboole_0(sK30)
    | r2_hidden(sK67(sK29,sK32,sK31),sK29) ),
    inference(duplicate_literal_removal,[],[f13330])).

fof(f13330,plain,
    ( v1_xboole_0(sK29)
    | v1_xboole_0(sK30)
    | r2_hidden(sK67(sK29,sK32,sK31),sK29)
    | v1_xboole_0(sK29) ),
    inference(resolution,[],[f3677,f2943])).

fof(f2943,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2319])).

fof(f2319,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1826])).

fof(f1826,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f3677,plain,
    ( m1_subset_1(sK67(sK29,sK32,sK31),sK29)
    | v1_xboole_0(sK29)
    | v1_xboole_0(sK30) ),
    inference(subsumption_resolution,[],[f3550,f2402])).

fof(f3550,plain,
    ( m1_subset_1(sK67(sK29,sK32,sK31),sK29)
    | ~ m1_subset_1(sK32,k1_zfmisc_1(k2_zfmisc_1(sK29,sK30)))
    | v1_xboole_0(sK29)
    | v1_xboole_0(sK30) ),
    inference(resolution,[],[f2403,f2524])).

fof(f2524,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK67(X1,X2,X3),X1)
      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2127])).

fof(f2127,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                    | ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) ) )
                  & ( ( r2_hidden(k4_tarski(sK67(X1,X2,X3),X3),X2)
                      & m1_subset_1(sK67(X1,X2,X3),X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK67])],[f2125,f2126])).

fof(f2126,plain,(
    ! [X3,X2,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X3),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(sK67(X1,X2,X3),X3),X2)
        & m1_subset_1(sK67(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f2125,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                    | ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) ) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f2124])).

fof(f2124,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                    | ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) ) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f1565])).

fof(f1565,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1261])).

fof(f1261,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f19115,plain,(
    ~ r2_hidden(sK67(sK29,sK32,sK31),sK29) ),
    inference(subsumption_resolution,[],[f19114,f4420])).

fof(f19114,plain,
    ( v1_xboole_0(sK30)
    | ~ r2_hidden(sK67(sK29,sK32,sK31),sK29) ),
    inference(subsumption_resolution,[],[f19110,f4450])).

fof(f19110,plain,
    ( v1_xboole_0(sK29)
    | v1_xboole_0(sK30)
    | ~ r2_hidden(sK67(sK29,sK32,sK31),sK29) ),
    inference(trivial_inequality_removal,[],[f18967])).

fof(f18967,plain,
    ( v1_xboole_0(sK29)
    | v1_xboole_0(sK30)
    | ~ r2_hidden(sK67(sK29,sK32,sK31),sK29)
    | sK31 != sK31 ),
    inference(resolution,[],[f3678,f3853])).

fof(f3853,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK32)
      | ~ r2_hidden(X6,sK29)
      | sK31 != X7 ) ),
    inference(subsumption_resolution,[],[f3852,f3209])).

fof(f3209,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2684])).

fof(f2684,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2214])).

fof(f2214,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK102(X0,X1),X3),X0)
            | ~ r2_hidden(sK102(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK102(X0,X1),sK103(X0,X1)),X0)
            | r2_hidden(sK102(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK104(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK102,sK103,sK104])],[f2210,f2213,f2212,f2211])).

fof(f2211,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK102(X0,X1),X3),X0)
          | ~ r2_hidden(sK102(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK102(X0,X1),X4),X0)
          | r2_hidden(sK102(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2212,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK102(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK102(X0,X1),sK103(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2213,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK104(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2210,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f2209])).

fof(f2209,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f3852,plain,(
    ! [X6,X7] :
      ( sK31 != X7
      | ~ r2_hidden(X6,sK29)
      | ~ r2_hidden(k4_tarski(X6,X7),sK32)
      | ~ r2_hidden(X6,k1_relat_1(sK32)) ) ),
    inference(subsumption_resolution,[],[f3851,f3476])).

fof(f3476,plain,(
    v1_relat_1(sK32) ),
    inference(resolution,[],[f2402,f2568])).

fof(f2568,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1600])).

fof(f1600,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3851,plain,(
    ! [X6,X7] :
      ( sK31 != X7
      | ~ r2_hidden(X6,sK29)
      | ~ r2_hidden(k4_tarski(X6,X7),sK32)
      | ~ r2_hidden(X6,k1_relat_1(sK32))
      | ~ v1_relat_1(sK32) ) ),
    inference(subsumption_resolution,[],[f3843,f2400])).

fof(f2400,plain,(
    v1_funct_1(sK32) ),
    inference(cnf_transformation,[],[f2038])).

fof(f3843,plain,(
    ! [X6,X7] :
      ( sK31 != X7
      | ~ r2_hidden(X6,sK29)
      | ~ r2_hidden(k4_tarski(X6,X7),sK32)
      | ~ r2_hidden(X6,k1_relat_1(sK32))
      | ~ v1_funct_1(sK32)
      | ~ v1_relat_1(sK32) ) ),
    inference(superposition,[],[f2404,f2480])).

fof(f2480,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2085])).

fof(f2085,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1542])).

fof(f1542,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1541])).

fof(f1541,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f903])).

fof(f903,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2404,plain,(
    ! [X4] :
      ( sK31 != k1_funct_1(sK32,X4)
      | ~ r2_hidden(X4,sK29) ) ),
    inference(cnf_transformation,[],[f2038])).

fof(f3678,plain,
    ( r2_hidden(k4_tarski(sK67(sK29,sK32,sK31),sK31),sK32)
    | v1_xboole_0(sK29)
    | v1_xboole_0(sK30) ),
    inference(subsumption_resolution,[],[f3551,f2402])).

fof(f3551,plain,
    ( r2_hidden(k4_tarski(sK67(sK29,sK32,sK31),sK31),sK32)
    | ~ m1_subset_1(sK32,k1_zfmisc_1(k2_zfmisc_1(sK29,sK30)))
    | v1_xboole_0(sK29)
    | v1_xboole_0(sK30) ),
    inference(resolution,[],[f2403,f2525])).

fof(f2525,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK67(X1,X2,X3),X3),X2)
      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2127])).
%------------------------------------------------------------------------------
