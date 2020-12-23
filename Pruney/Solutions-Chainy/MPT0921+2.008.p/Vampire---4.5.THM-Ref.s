%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 365 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   23
%              Number of atoms          :  480 (2519 expanded)
%              Number of equality atoms :  304 (1547 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f118,f164,f235,f363])).

fof(f363,plain,
    ( spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f254,f254,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 )
    | ~ spl10_6 ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( ! [X0] :
        ( sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
        | sK5 != sK5
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 )
    | ~ spl10_6 ),
    inference(resolution,[],[f95,f76])).

fof(f76,plain,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl10_6
  <=> m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | sK5 != X0
      | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 ) ),
    inference(global_subsumption,[],[f15,f16,f17,f18,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
      | k1_xboole_0 = sK0
      | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
      | k1_xboole_0 = sK0
      | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 ) ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK5 != X0
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3))
      | k1_xboole_0 = X1
      | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2 ) ),
    inference(global_subsumption,[],[f16,f17,f18,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2 ) ),
    inference(resolution,[],[f89,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2 ) ),
    inference(global_subsumption,[],[f17,f18,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2 ) ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2)
      | ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k9_mcart_1(X0,X1,X2,sK3,X4) = X3 ) ),
    inference(global_subsumption,[],[f18,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | k9_mcart_1(X0,X1,X2,sK3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | k9_mcart_1(X0,X1,X2,sK3,X4) = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | k9_mcart_1(X0,X1,X2,sK3,X4) = X3 ) ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),sK3)
      | ~ m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),sK2)
      | sK5 != X5
      | ~ m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),sK0)
      | sK4 = sK8(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(superposition,[],[f13,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f254,plain,
    ( ! [X0] : sK4 != X0
    | spl10_5
    | ~ spl10_8 ),
    inference(superposition,[],[f71,f238])).

fof(f238,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl10_8 ),
    inference(superposition,[],[f109,f109])).

fof(f109,plain,
    ( ! [X2] : k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl10_8
  <=> ! [X2] : k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f71,plain,
    ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_5
  <=> sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f235,plain,
    ( spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f51,f56,f61,f66,f71,f76,f163])).

fof(f163,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15))
        | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5)
        | k1_xboole_0 = X15
        | k1_xboole_0 = X14
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12 )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_14
  <=> ! [X13,X15,X12,X14] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15))
        | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5)
        | k1_xboole_0 = X15
        | k1_xboole_0 = X14
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f66,plain,
    ( k1_xboole_0 != sK3
    | spl10_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f61,plain,
    ( k1_xboole_0 != sK2
    | spl10_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f51,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f164,plain,
    ( spl10_8
    | spl10_14
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f122,f116,f162,f108])).

fof(f116,plain,
    ( spl10_10
  <=> ! [X1] :
        ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5))
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f122,plain,
    ( ! [X14,X12,X15,X13,X11] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15))
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14
        | k1_xboole_0 = X15
        | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5)
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X11 )
    | ~ spl10_10 ),
    inference(superposition,[],[f45,f117])).

fof(f117,plain,
    ( ! [X1] :
        ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5))
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f45,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f118,plain,
    ( spl10_4
    | spl10_3
    | spl10_2
    | spl10_1
    | ~ spl10_6
    | spl10_10
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f106,f74,f116,f74,f49,f54,f59,f64])).

fof(f106,plain,
    ( ! [X1] :
        ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK3
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 )
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ! [X1] :
        ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK3
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 )
    | ~ spl10_6 ),
    inference(superposition,[],[f42,f101])).

fof(f77,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f14,f32])).

fof(f14,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f19,f69])).

fof(f19,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f18,f64])).

fof(f62,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f17,f59])).

fof(f57,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f16,f54])).

fof(f52,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f15,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (14372)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (14390)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (14366)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (14390)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f367,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f118,f164,f235,f363])).
% 0.21/0.55  fof(f363,plain,(
% 0.21/0.55    spl10_5 | ~spl10_6 | ~spl10_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    $false | (spl10_5 | ~spl10_6 | ~spl10_8)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f254,f254,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) ) | ~spl10_6),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X0] : (sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | sK5 != sK5 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) ) | ~spl10_6),
% 0.21/0.55    inference(resolution,[],[f95,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl10_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    spl10_6 <=> m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | sK5 != X0 | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1) )),
% 0.21/0.55    inference(global_subsumption,[],[f15,f16,f17,f18,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,X0) = X1) )),
% 0.21/0.55    inference(resolution,[],[f92,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f31,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f21,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK5 != X0 | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3)) | k1_xboole_0 = X1 | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2) )),
% 0.21/0.55    inference(global_subsumption,[],[f16,f17,f18,f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2),sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(X1,sK1,sK2,sK3,X0) = X2) )),
% 0.21/0.55    inference(resolution,[],[f89,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f30,f32])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2) )),
% 0.21/0.55    inference(global_subsumption,[],[f17,f18,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(X0,X1,sK2,sK3,X3) = X2) )),
% 0.21/0.55    inference(resolution,[],[f86,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f29,f32])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | ~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k9_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.55    inference(global_subsumption,[],[f18,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k9_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k9_mcart_1(X0,X1,X2,sK3,X4) = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k9_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.55    inference(resolution,[],[f79,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f26,f32])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),sK3) | ~m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),sK1) | ~m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),sK2) | sK5 != X5 | ~m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),sK0) | sK4 = sK8(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(superposition,[],[f13,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f27,f32])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X8) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(flattening,[],[f7])).
% 0.21/0.55  fof(f7,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f5])).
% 0.21/0.55  fof(f5,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    k1_xboole_0 != sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    ( ! [X0] : (sK4 != X0) ) | (spl10_5 | ~spl10_8)),
% 0.21/0.55    inference(superposition,[],[f71,f238])).
% 0.21/0.55  fof(f238,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 = X1) ) | ~spl10_8),
% 0.21/0.55    inference(superposition,[],[f109,f109])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X2] : (k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) ) | ~spl10_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    spl10_8 <=> ! [X2] : k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | spl10_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    spl10_5 <=> sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.55  fof(f235,plain,(
% 0.21/0.55    spl10_1 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_6 | ~spl10_14),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    $false | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_6 | ~spl10_14)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f51,f56,f61,f66,f71,f76,f163])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15)) | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5) | k1_xboole_0 = X15 | k1_xboole_0 = X14 | k1_xboole_0 = X13 | k1_xboole_0 = X12) ) | ~spl10_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f162])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    spl10_14 <=> ! [X13,X15,X12,X14] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15)) | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5) | k1_xboole_0 = X15 | k1_xboole_0 = X14 | k1_xboole_0 = X13 | k1_xboole_0 = X12)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    k1_xboole_0 != sK3 | spl10_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl10_4 <=> k1_xboole_0 = sK3),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    k1_xboole_0 != sK2 | spl10_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    spl10_3 <=> k1_xboole_0 = sK2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl10_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    spl10_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    k1_xboole_0 != sK0 | spl10_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    spl10_1 <=> k1_xboole_0 = sK0),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    spl10_8 | spl10_14 | ~spl10_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f122,f116,f162,f108])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    spl10_10 <=> ! [X1] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X14,X12,X15,X13,X11] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15)) | k1_xboole_0 = X12 | k1_xboole_0 = X13 | k1_xboole_0 = X14 | k1_xboole_0 = X15 | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X11) ) | ~spl10_10),
% 0.21/0.55    inference(superposition,[],[f45,f117])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X1] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) ) | ~spl10_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f116])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7) )),
% 0.21/0.55    inference(equality_resolution,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.21/0.55    inference(definition_unfolding,[],[f24,f32])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl10_4 | spl10_3 | spl10_2 | spl10_1 | ~spl10_6 | spl10_10 | ~spl10_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f106,f74,f116,f74,f49,f54,f59,f64])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X1] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5)) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) ) | ~spl10_6),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X1] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK4,sK9(sK0,sK1,sK2,sK3,X1,sK5)) | ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) ) | ~spl10_6),
% 0.21/0.55    inference(superposition,[],[f42,f101])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    spl10_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f33,f74])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.55    inference(definition_unfolding,[],[f14,f32])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ~spl10_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f19,f69])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ~spl10_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f18,f64])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ~spl10_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f17,f59])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ~spl10_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f16,f54])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ~spl10_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f15,f49])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (14390)------------------------------
% 0.21/0.56  % (14390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14390)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (14390)Memory used [KB]: 11129
% 0.21/0.56  % (14390)Time elapsed: 0.111 s
% 0.21/0.56  % (14390)------------------------------
% 0.21/0.56  % (14390)------------------------------
% 0.21/0.56  % (14362)Success in time 0.198 s
%------------------------------------------------------------------------------
