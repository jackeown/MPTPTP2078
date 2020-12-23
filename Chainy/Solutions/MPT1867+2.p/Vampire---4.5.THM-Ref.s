%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1867+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 3.64s
% Output     : Refutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 189 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 ( 972 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10294,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10236,f6972])).

fof(f6972,plain,(
    k1_xboole_0 != sK17(sK14,k1_xboole_0) ),
    inference(backward_demodulation,[],[f6345,f6826])).

fof(f6826,plain,(
    ! [X0] : k1_xboole_0 = k9_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f5328,f5328,f5328,f5811,f5811,f4881])).

fof(f4881,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_subset_1(X0,X2,X3) = X1
      | r2_hidden(sK84(X0,X1,X2,X3),X2)
      | r2_hidden(sK84(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f4345])).

fof(f4345,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ( ( ~ r2_hidden(sK84(X0,X1,X2,X3),X3)
                  | ~ r2_hidden(sK84(X0,X1,X2,X3),X2)
                  | ~ r2_hidden(sK84(X0,X1,X2,X3),X1) )
                & ( ( r2_hidden(sK84(X0,X1,X2,X3),X3)
                    & r2_hidden(sK84(X0,X1,X2,X3),X2) )
                  | r2_hidden(sK84(X0,X1,X2,X3),X1) )
                & m1_subset_1(sK84(X0,X1,X2,X3),X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK84])],[f4343,f4344])).

fof(f4344,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X4,X3)
            | ~ r2_hidden(X4,X2)
            | ~ r2_hidden(X4,X1) )
          & ( ( r2_hidden(X4,X3)
              & r2_hidden(X4,X2) )
            | r2_hidden(X4,X1) )
          & m1_subset_1(X4,X0) )
     => ( ( ~ r2_hidden(sK84(X0,X1,X2,X3),X3)
          | ~ r2_hidden(sK84(X0,X1,X2,X3),X2)
          | ~ r2_hidden(sK84(X0,X1,X2,X3),X1) )
        & ( ( r2_hidden(sK84(X0,X1,X2,X3),X3)
            & r2_hidden(sK84(X0,X1,X2,X3),X2) )
          | r2_hidden(sK84(X0,X1,X2,X3),X1) )
        & m1_subset_1(sK84(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4343,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,X1) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | r2_hidden(X4,X1) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4342])).

fof(f4342,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,X1) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | r2_hidden(X4,X1) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f3869])).

fof(f3869,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( r2_hidden(X4,X1)
                  <~> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f3868])).

fof(f3868,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( r2_hidden(X4,X1)
                  <~> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f499])).

fof(f499,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_subset_1)).

fof(f5811,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f5789,f5798])).

fof(f5798,plain,(
    k1_xboole_0 = sK15 ),
    inference(unit_resulting_resolution,[],[f4525,f4608])).

fof(f4608,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3747])).

fof(f3747,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f4525,plain,(
    v1_xboole_0(sK15) ),
    inference(cnf_transformation,[],[f4181])).

fof(f4181,plain,
    ( ~ v2_tex_2(sK15,sK14)
    & m1_subset_1(sK15,k1_zfmisc_1(u1_struct_0(sK14)))
    & v1_xboole_0(sK15)
    & l1_pre_topc(sK14)
    & v2_pre_topc(sK14)
    & ~ v2_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f3694,f4180,f4179])).

fof(f4179,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK14)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK14)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK14)
      & v2_pre_topc(sK14)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f4180,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK14)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK14)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK15,sK14)
      & m1_subset_1(sK15,k1_zfmisc_1(u1_struct_0(sK14)))
      & v1_xboole_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f3694,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3693])).

fof(f3693,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3678])).

fof(f3678,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f3677])).

fof(f3677,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f5789,plain,(
    ! [X0] : ~ r2_hidden(X0,sK15) ),
    inference(unit_resulting_resolution,[],[f4525,f4604])).

fof(f4604,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4232])).

fof(f4232,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK35(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35])],[f4230,f4231])).

fof(f4231,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK35(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4230,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f4229])).

fof(f4229,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f5328,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f6345,plain,(
    k9_subset_1(u1_struct_0(sK14),k1_xboole_0,k1_xboole_0) != sK17(sK14,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f4524,f5805,f5328,f5328,f5636,f4545])).

fof(f4545,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK17(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4190])).

fof(f4190,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK17(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK17(X0,X1),X1)
                & m1_subset_1(sK17(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK18(X0,X1,X4)) = X4
                    & v3_pre_topc(sK18(X0,X1,X4),X0)
                    & m1_subset_1(sK18(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f4187,f4189,f4188])).

fof(f4188,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK17(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK17(X0,X1),X1)
        & m1_subset_1(sK17(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4189,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK18(X0,X1,X4)) = X4
        & v3_pre_topc(sK18(X0,X1,X4),X0)
        & m1_subset_1(sK18(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4187,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f4186])).

fof(f4186,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3706])).

fof(f3706,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3705])).

fof(f3705,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3605])).

fof(f3605,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f5636,plain,(
    v3_pre_topc(k1_xboole_0,sK14) ),
    inference(unit_resulting_resolution,[],[f4523,f4618,f5328,f4524,f4978])).

fof(f4978,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3930])).

fof(f3930,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3929])).

fof(f3929,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2086])).

fof(f2086,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f4618,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4523,plain,(
    v2_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f4181])).

fof(f5805,plain,(
    ~ v2_tex_2(k1_xboole_0,sK14) ),
    inference(backward_demodulation,[],[f4527,f5798])).

fof(f4527,plain,(
    ~ v2_tex_2(sK15,sK14) ),
    inference(cnf_transformation,[],[f4181])).

fof(f4524,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f4181])).

fof(f10236,plain,(
    k1_xboole_0 = sK17(sK14,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f4952,f6005,f4941])).

fof(f4941,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4372])).

fof(f4372,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f4371])).

fof(f4371,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6005,plain,(
    r1_tarski(sK17(sK14,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f4524,f5328,f5805,f4544])).

fof(f4544,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK17(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4190])).

fof(f4952,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
