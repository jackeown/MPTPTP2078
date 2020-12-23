%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1241+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 7.18s
% Output     : Refutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 381 expanded)
%              Number of leaves         :   20 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          :  353 (2917 expanded)
%              Number of equality atoms :   83 ( 759 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4467,f4534,f4589,f4638,f7837,f8076])).

fof(f8076,plain,
    ( spl87_2
    | ~ spl87_3 ),
    inference(avatar_contradiction_clause,[],[f8075])).

fof(f8075,plain,
    ( $false
    | spl87_2
    | ~ spl87_3 ),
    inference(subsumption_resolution,[],[f7985,f4511])).

fof(f4511,plain,
    ( k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),sK20) != k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),sK20))
    | spl87_2 ),
    inference(subsumption_resolution,[],[f4500,f4466])).

fof(f4466,plain,
    ( ~ v3_pre_topc(sK20,sK18)
    | spl87_2 ),
    inference(avatar_component_clause,[],[f4465])).

fof(f4465,plain,
    ( spl87_2
  <=> v3_pre_topc(sK20,sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_2])])).

fof(f4500,plain,
    ( k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),sK20) != k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),sK20))
    | v3_pre_topc(sK20,sK18) ),
    inference(backward_demodulation,[],[f3974,f4474])).

fof(f4474,plain,(
    u1_struct_0(sK18) = k2_struct_0(sK18) ),
    inference(resolution,[],[f3615,f2909])).

fof(f2909,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2232])).

fof(f2232,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3615,plain,(
    l1_struct_0(sK18) ),
    inference(resolution,[],[f2789,f3297])).

fof(f3297,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2483])).

fof(f2483,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2789,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f2560])).

fof(f2560,plain,
    ( ( ( ~ v3_pre_topc(sK20,sK18)
        & sK20 = k1_tops_1(sK18,sK20) )
      | ( sK21 != k1_tops_1(sK19,sK21)
        & v3_pre_topc(sK21,sK19) ) )
    & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    & m1_subset_1(sK20,k1_zfmisc_1(u1_struct_0(sK18)))
    & l1_pre_topc(sK19)
    & l1_pre_topc(sK18)
    & v2_pre_topc(sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21])],[f2132,f2559,f2558,f2557,f2556])).

fof(f2556,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v3_pre_topc(X2,X0)
                        & k1_tops_1(X0,X2) = X2 )
                      | ( k1_tops_1(X1,X3) != X3
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,sK18)
                      & k1_tops_1(sK18,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK18))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK18)
      & v2_pre_topc(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f2557,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v3_pre_topc(X2,sK18)
                    & k1_tops_1(sK18,X2) = X2 )
                  | ( k1_tops_1(X1,X3) != X3
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK18))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v3_pre_topc(X2,sK18)
                  & k1_tops_1(sK18,X2) = X2 )
                | ( k1_tops_1(sK19,X3) != X3
                  & v3_pre_topc(X3,sK19) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK18))) )
      & l1_pre_topc(sK19) ) ),
    introduced(choice_axiom,[])).

fof(f2558,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ v3_pre_topc(X2,sK18)
                & k1_tops_1(sK18,X2) = X2 )
              | ( k1_tops_1(sK19,X3) != X3
                & v3_pre_topc(X3,sK19) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK18))) )
   => ( ? [X3] :
          ( ( ( ~ v3_pre_topc(sK20,sK18)
              & sK20 = k1_tops_1(sK18,sK20) )
            | ( k1_tops_1(sK19,X3) != X3
              & v3_pre_topc(X3,sK19) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
      & m1_subset_1(sK20,k1_zfmisc_1(u1_struct_0(sK18))) ) ),
    introduced(choice_axiom,[])).

fof(f2559,plain,
    ( ? [X3] :
        ( ( ( ~ v3_pre_topc(sK20,sK18)
            & sK20 = k1_tops_1(sK18,sK20) )
          | ( k1_tops_1(sK19,X3) != X3
            & v3_pre_topc(X3,sK19) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK19))) )
   => ( ( ( ~ v3_pre_topc(sK20,sK18)
          & sK20 = k1_tops_1(sK18,sK20) )
        | ( sK21 != k1_tops_1(sK19,sK21)
          & v3_pre_topc(sK21,sK19) ) )
      & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19))) ) ),
    introduced(choice_axiom,[])).

fof(f2132,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2131])).

fof(f2131,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2124])).

fof(f2124,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2123])).

fof(f2123,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f3974,plain,
    ( v3_pre_topc(sK20,sK18)
    | k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),sK20) != k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),sK20)) ),
    inference(subsumption_resolution,[],[f3973,f2789])).

fof(f3973,plain,
    ( v3_pre_topc(sK20,sK18)
    | k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),sK20) != k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),sK20))
    | ~ l1_pre_topc(sK18) ),
    inference(subsumption_resolution,[],[f3731,f2788])).

fof(f2788,plain,(
    v2_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f2560])).

fof(f3731,plain,
    ( v3_pre_topc(sK20,sK18)
    | k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),sK20) != k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),sK20))
    | ~ v2_pre_topc(sK18)
    | ~ l1_pre_topc(sK18) ),
    inference(resolution,[],[f2791,f2894])).

fof(f2894,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2215])).

fof(f2215,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2214])).

fof(f2214,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1844])).

fof(f1844,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f2791,plain,(
    m1_subset_1(sK20,k1_zfmisc_1(u1_struct_0(sK18))) ),
    inference(cnf_transformation,[],[f2560])).

fof(f7985,plain,
    ( k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),sK20) = k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),sK20))
    | ~ spl87_3 ),
    inference(backward_demodulation,[],[f5272,f4533])).

fof(f4533,plain,
    ( sK20 = k1_tops_1(sK18,sK20)
    | ~ spl87_3 ),
    inference(avatar_component_clause,[],[f4532])).

fof(f4532,plain,
    ( spl87_3
  <=> sK20 = k1_tops_1(sK18,sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_3])])).

fof(f5272,plain,(
    k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),k1_tops_1(sK18,sK20)) = k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),u1_struct_0(sK18),k1_tops_1(sK18,sK20))) ),
    inference(forward_demodulation,[],[f5271,f4474])).

fof(f5271,plain,(
    k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),k1_tops_1(sK18,sK20)) = k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),k1_tops_1(sK18,sK20))) ),
    inference(subsumption_resolution,[],[f5270,f2789])).

fof(f5270,plain,
    ( k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),k1_tops_1(sK18,sK20)) = k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),k1_tops_1(sK18,sK20)))
    | ~ l1_pre_topc(sK18) ),
    inference(subsumption_resolution,[],[f5244,f3923])).

fof(f3923,plain,(
    m1_subset_1(k1_tops_1(sK18,sK20),k1_zfmisc_1(u1_struct_0(sK18))) ),
    inference(subsumption_resolution,[],[f3695,f2789])).

fof(f3695,plain,
    ( m1_subset_1(k1_tops_1(sK18,sK20),k1_zfmisc_1(u1_struct_0(sK18)))
    | ~ l1_pre_topc(sK18) ),
    inference(resolution,[],[f2791,f2798])).

fof(f2798,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2136])).

fof(f2136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2135])).

fof(f2135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2088])).

fof(f2088,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f5244,plain,
    ( k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),k1_tops_1(sK18,sK20)) = k2_pre_topc(sK18,k7_subset_1(u1_struct_0(sK18),k2_struct_0(sK18),k1_tops_1(sK18,sK20)))
    | ~ m1_subset_1(k1_tops_1(sK18,sK20),k1_zfmisc_1(u1_struct_0(sK18)))
    | ~ l1_pre_topc(sK18) ),
    inference(resolution,[],[f3925,f2893])).

fof(f2893,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2215])).

fof(f3925,plain,(
    v3_pre_topc(k1_tops_1(sK18,sK20),sK18) ),
    inference(subsumption_resolution,[],[f3924,f2788])).

fof(f3924,plain,
    ( v3_pre_topc(k1_tops_1(sK18,sK20),sK18)
    | ~ v2_pre_topc(sK18) ),
    inference(subsumption_resolution,[],[f3696,f2789])).

fof(f3696,plain,
    ( v3_pre_topc(k1_tops_1(sK18,sK20),sK18)
    | ~ l1_pre_topc(sK18)
    | ~ v2_pre_topc(sK18) ),
    inference(resolution,[],[f2791,f2799])).

fof(f2799,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2138])).

fof(f2138,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2137])).

fof(f2137,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2097])).

fof(f2097,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f7837,plain,
    ( ~ spl87_1
    | spl87_4 ),
    inference(avatar_contradiction_clause,[],[f7836])).

fof(f7836,plain,
    ( $false
    | ~ spl87_1
    | spl87_4 ),
    inference(subsumption_resolution,[],[f7835,f4588])).

fof(f4588,plain,
    ( sK21 != k1_tops_1(sK19,sK21)
    | spl87_4 ),
    inference(avatar_component_clause,[],[f4587])).

fof(f4587,plain,
    ( spl87_4
  <=> sK21 = k1_tops_1(sK19,sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_4])])).

fof(f7835,plain,
    ( sK21 = k1_tops_1(sK19,sK21)
    | ~ spl87_1 ),
    inference(forward_demodulation,[],[f7834,f4446])).

fof(f4446,plain,(
    sK21 = k3_subset_1(u1_struct_0(sK19),k4_xboole_0(u1_struct_0(sK19),sK21)) ),
    inference(backward_demodulation,[],[f4308,f4309])).

fof(f4309,plain,(
    k3_subset_1(u1_struct_0(sK19),sK21) = k4_xboole_0(u1_struct_0(sK19),sK21) ),
    inference(resolution,[],[f2792,f2995])).

fof(f2995,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2302])).

fof(f2302,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2792,plain,(
    m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19))) ),
    inference(cnf_transformation,[],[f2560])).

fof(f4308,plain,(
    sK21 = k3_subset_1(u1_struct_0(sK19),k3_subset_1(u1_struct_0(sK19),sK21)) ),
    inference(resolution,[],[f2792,f2994])).

fof(f2994,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2301])).

fof(f2301,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f7834,plain,
    ( k1_tops_1(sK19,sK21) = k3_subset_1(u1_struct_0(sK19),k4_xboole_0(u1_struct_0(sK19),sK21))
    | ~ spl87_1 ),
    inference(backward_demodulation,[],[f4447,f7831])).

fof(f7831,plain,
    ( k4_xboole_0(u1_struct_0(sK19),sK21) = k2_pre_topc(sK19,k4_xboole_0(u1_struct_0(sK19),sK21))
    | ~ spl87_1 ),
    inference(subsumption_resolution,[],[f7830,f2790])).

fof(f2790,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f2560])).

fof(f7830,plain,
    ( k4_xboole_0(u1_struct_0(sK19),sK21) = k2_pre_topc(sK19,k4_xboole_0(u1_struct_0(sK19),sK21))
    | ~ l1_pre_topc(sK19)
    | ~ spl87_1 ),
    inference(subsumption_resolution,[],[f7807,f4458])).

fof(f4458,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK19),sK21),k1_zfmisc_1(u1_struct_0(sK19))) ),
    inference(forward_demodulation,[],[f4310,f4309])).

fof(f4310,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK19),sK21),k1_zfmisc_1(u1_struct_0(sK19))) ),
    inference(resolution,[],[f2792,f2996])).

fof(f2996,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2303])).

fof(f2303,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f7807,plain,
    ( k4_xboole_0(u1_struct_0(sK19),sK21) = k2_pre_topc(sK19,k4_xboole_0(u1_struct_0(sK19),sK21))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK19),sK21),k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ l1_pre_topc(sK19)
    | ~ spl87_1 ),
    inference(resolution,[],[f4566,f2969])).

fof(f2969,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2277])).

fof(f2277,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2276])).

fof(f2276,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f4566,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK19),sK21),sK19)
    | ~ spl87_1 ),
    inference(forward_demodulation,[],[f4565,f4309])).

fof(f4565,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK19),sK21),sK19)
    | ~ spl87_1 ),
    inference(subsumption_resolution,[],[f4564,f2790])).

fof(f4564,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK19),sK21),sK19)
    | ~ l1_pre_topc(sK19)
    | ~ spl87_1 ),
    inference(subsumption_resolution,[],[f4541,f2792])).

fof(f4541,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK19),sK21),sK19)
    | ~ m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK19)))
    | ~ l1_pre_topc(sK19)
    | ~ spl87_1 ),
    inference(resolution,[],[f4463,f2830])).

fof(f2830,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2574])).

fof(f2574,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2171])).

fof(f2171,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2104])).

fof(f2104,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f4463,plain,
    ( v3_pre_topc(sK21,sK19)
    | ~ spl87_1 ),
    inference(avatar_component_clause,[],[f4462])).

fof(f4462,plain,
    ( spl87_1
  <=> v3_pre_topc(sK21,sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl87_1])])).

fof(f4447,plain,(
    k1_tops_1(sK19,sK21) = k3_subset_1(u1_struct_0(sK19),k2_pre_topc(sK19,k4_xboole_0(u1_struct_0(sK19),sK21))) ),
    inference(backward_demodulation,[],[f4337,f4309])).

fof(f4337,plain,(
    k1_tops_1(sK19,sK21) = k3_subset_1(u1_struct_0(sK19),k2_pre_topc(sK19,k3_subset_1(u1_struct_0(sK19),sK21))) ),
    inference(subsumption_resolution,[],[f4110,f2790])).

fof(f4110,plain,
    ( k1_tops_1(sK19,sK21) = k3_subset_1(u1_struct_0(sK19),k2_pre_topc(sK19,k3_subset_1(u1_struct_0(sK19),sK21)))
    | ~ l1_pre_topc(sK19) ),
    inference(resolution,[],[f2792,f2813])).

fof(f2813,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2150])).

fof(f2150,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f4638,plain,
    ( ~ spl87_4
    | spl87_3 ),
    inference(avatar_split_clause,[],[f2794,f4532,f4587])).

fof(f2794,plain,
    ( sK20 = k1_tops_1(sK18,sK20)
    | sK21 != k1_tops_1(sK19,sK21) ),
    inference(cnf_transformation,[],[f2560])).

fof(f4589,plain,
    ( ~ spl87_4
    | ~ spl87_2 ),
    inference(avatar_split_clause,[],[f2796,f4465,f4587])).

fof(f2796,plain,
    ( ~ v3_pre_topc(sK20,sK18)
    | sK21 != k1_tops_1(sK19,sK21) ),
    inference(cnf_transformation,[],[f2560])).

fof(f4534,plain,
    ( spl87_1
    | spl87_3 ),
    inference(avatar_split_clause,[],[f2793,f4532,f4462])).

fof(f2793,plain,
    ( sK20 = k1_tops_1(sK18,sK20)
    | v3_pre_topc(sK21,sK19) ),
    inference(cnf_transformation,[],[f2560])).

fof(f4467,plain,
    ( spl87_1
    | ~ spl87_2 ),
    inference(avatar_split_clause,[],[f2795,f4465,f4462])).

fof(f2795,plain,
    ( ~ v3_pre_topc(sK20,sK18)
    | v3_pre_topc(sK21,sK19) ),
    inference(cnf_transformation,[],[f2560])).
%------------------------------------------------------------------------------
