%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1293+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 4.91s
% Output     : Refutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 210 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  319 ( 587 expanded)
%              Number of equality atoms :   32 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4260,f4270,f4290,f4505,f6761,f6802,f8402])).

fof(f8402,plain,
    ( spl176_64
    | ~ spl176_69 ),
    inference(avatar_contradiction_clause,[],[f8401])).

fof(f8401,plain,
    ( $false
    | spl176_64
    | ~ spl176_69 ),
    inference(subsumption_resolution,[],[f8400,f4420])).

fof(f4420,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3641,f3194])).

fof(f3194,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f2259])).

fof(f2259,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f3641,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f8400,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k1_xboole_0)
    | spl176_64
    | ~ spl176_69 ),
    inference(forward_demodulation,[],[f8399,f7266])).

fof(f7266,plain,(
    ! [X12,X11] : k1_xboole_0 = k4_xboole_0(k3_tarski(X11),k3_tarski(k2_xboole_0(X11,X12))) ),
    inference(superposition,[],[f3369,f3666])).

fof(f3666,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f445])).

fof(f445,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f3369,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f8399,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))))
    | spl176_64
    | ~ spl176_69 ),
    inference(forward_demodulation,[],[f8398,f3832])).

fof(f3832,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f8398,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))))
    | spl176_64
    | ~ spl176_69 ),
    inference(forward_demodulation,[],[f8397,f3362])).

fof(f3362,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f8397,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))))
    | spl176_64
    | ~ spl176_69 ),
    inference(forward_demodulation,[],[f8396,f3666])).

fof(f8396,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))))
    | spl176_64
    | ~ spl176_69 ),
    inference(forward_demodulation,[],[f8380,f3329])).

fof(f3329,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f8380,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))))
    | spl176_64
    | ~ spl176_69 ),
    inference(unit_resulting_resolution,[],[f6801,f6760,f4083])).

fof(f4083,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f3299])).

fof(f3299,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2865])).

fof(f2865,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK20(X0,X1,X2),X1)
            | ~ r2_hidden(sK20(X0,X1,X2),X0)
            | ~ r2_hidden(sK20(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK20(X0,X1,X2),X1)
              & r2_hidden(sK20(X0,X1,X2),X0) )
            | r2_hidden(sK20(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f2863,f2864])).

fof(f2864,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK20(X0,X1,X2),X1)
          | ~ r2_hidden(sK20(X0,X1,X2),X0)
          | ~ r2_hidden(sK20(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK20(X0,X1,X2),X1)
            & r2_hidden(sK20(X0,X1,X2),X0) )
          | r2_hidden(sK20(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2863,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f2862])).

fof(f2862,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f2861])).

fof(f2861,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f6760,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k3_tarski(k4_xboole_0(sK1,sK2)))
    | spl176_64 ),
    inference(avatar_component_clause,[],[f6758])).

fof(f6758,plain,
    ( spl176_64
  <=> r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl176_64])])).

fof(f6801,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)))
    | ~ spl176_69 ),
    inference(avatar_component_clause,[],[f6799])).

fof(f6799,plain,
    ( spl176_69
  <=> r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl176_69])])).

fof(f6802,plain,
    ( spl176_69
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9
    | ~ spl176_23 ),
    inference(avatar_split_clause,[],[f4897,f4502,f4287,f4267,f4257,f6799])).

fof(f4257,plain,
    ( spl176_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl176_3])])).

fof(f4267,plain,
    ( spl176_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl176_5])])).

fof(f4287,plain,
    ( spl176_9
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl176_9])])).

fof(f4502,plain,
    ( spl176_23
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl176_23])])).

fof(f4897,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9
    | ~ spl176_23 ),
    inference(backward_demodulation,[],[f4546,f4829])).

fof(f4829,plain,
    ( ! [X0] : k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0))
    | ~ spl176_3 ),
    inference(unit_resulting_resolution,[],[f4396,f3242])).

fof(f3242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2293])).

fof(f2293,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f581,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f4396,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl176_3 ),
    inference(backward_demodulation,[],[f4346,f4391])).

fof(f4391,plain,
    ( ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl176_3 ),
    inference(unit_resulting_resolution,[],[f4259,f3213])).

fof(f3213,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2266])).

fof(f2266,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f4259,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl176_3 ),
    inference(avatar_component_clause,[],[f4257])).

fof(f4346,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl176_3 ),
    inference(unit_resulting_resolution,[],[f4259,f3214])).

fof(f3214,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2267])).

fof(f2267,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f470])).

fof(f470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f4546,plain,
    ( r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9
    | ~ spl176_23 ),
    inference(backward_demodulation,[],[f4399,f4527])).

fof(f4527,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0)
    | ~ spl176_23 ),
    inference(unit_resulting_resolution,[],[f4504,f3213])).

fof(f4504,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl176_23 ),
    inference(avatar_component_clause,[],[f4502])).

fof(f4399,plain,
    ( r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))),k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9 ),
    inference(backward_demodulation,[],[f4371,f4391])).

fof(f4371,plain,
    ( r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9 ),
    inference(backward_demodulation,[],[f4364,f4358])).

fof(f4358,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl176_3 ),
    inference(unit_resulting_resolution,[],[f4259,f3242])).

fof(f4364,plain,
    ( r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)))
    | ~ spl176_5
    | spl176_9 ),
    inference(backward_demodulation,[],[f4329,f4359])).

fof(f4359,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl176_5 ),
    inference(unit_resulting_resolution,[],[f4269,f3242])).

fof(f4269,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl176_5 ),
    inference(avatar_component_clause,[],[f4267])).

fof(f4329,plain,
    ( r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)))
    | spl176_9 ),
    inference(unit_resulting_resolution,[],[f4289,f3202])).

fof(f3202,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2814])).

fof(f2814,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2812,f2813])).

fof(f2813,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2812,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2811])).

fof(f2811,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2260])).

fof(f2260,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f4289,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl176_9 ),
    inference(avatar_component_clause,[],[f4287])).

fof(f6761,plain,
    ( ~ spl176_64
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9
    | ~ spl176_23 ),
    inference(avatar_split_clause,[],[f4898,f4502,f4287,f4267,f4257,f6758])).

fof(f4898,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9
    | ~ spl176_23 ),
    inference(backward_demodulation,[],[f4545,f4829])).

fof(f4545,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9
    | ~ spl176_23 ),
    inference(backward_demodulation,[],[f4398,f4527])).

fof(f4398,plain,
    ( ~ r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9 ),
    inference(backward_demodulation,[],[f4372,f4391])).

fof(f4372,plain,
    ( ~ r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ spl176_3
    | ~ spl176_5
    | spl176_9 ),
    inference(backward_demodulation,[],[f4363,f4358])).

fof(f4363,plain,
    ( ~ r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ spl176_5
    | spl176_9 ),
    inference(backward_demodulation,[],[f4335,f4359])).

fof(f4335,plain,
    ( ~ r2_hidden(sK4(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl176_9 ),
    inference(unit_resulting_resolution,[],[f4289,f3203])).

fof(f3203,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2814])).

fof(f4505,plain,
    ( spl176_23
    | ~ spl176_3 ),
    inference(avatar_split_clause,[],[f4373,f4257,f4502])).

fof(f4373,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl176_3 ),
    inference(backward_demodulation,[],[f4355,f4358])).

fof(f4355,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl176_3 ),
    inference(unit_resulting_resolution,[],[f4259,f3241])).

fof(f3241,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2292])).

fof(f2292,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f563])).

fof(f563,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f4290,plain,(
    ~ spl176_9 ),
    inference(avatar_split_clause,[],[f3192,f4287])).

fof(f3192,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f2805])).

fof(f2805,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2256,f2804,f2803,f2802])).

fof(f2802,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2803,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f2804,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f2256,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2247])).

fof(f2247,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f2246])).

fof(f2246,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

fof(f4270,plain,(
    spl176_5 ),
    inference(avatar_split_clause,[],[f3191,f4267])).

fof(f3191,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2805])).

fof(f4260,plain,(
    spl176_3 ),
    inference(avatar_split_clause,[],[f3190,f4257])).

fof(f3190,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2805])).
%------------------------------------------------------------------------------
