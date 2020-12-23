%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1401+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:52 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 378 expanded)
%              Number of leaves         :   14 ( 149 expanded)
%              Depth                    :   13
%              Number of atoms          :  403 (3718 expanded)
%              Number of equality atoms :   48 ( 419 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f132,f84])).

fof(f84,plain,(
    ~ m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f81,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    ~ r1_tarski(k1_connsp_2(sK2,sK3),sK4) ),
    inference(unit_resulting_resolution,[],[f43,f44,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f44,plain,(
    k1_connsp_2(sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f23])).

% (16631)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f23,plain,
    ( k1_connsp_2(sK2,sK3) != sK4
    & r1_tarski(sK4,k1_connsp_2(sK2,sK3))
    & r2_hidden(sK3,sK4)
    & v4_pre_topc(sK4,sK2)
    & v3_pre_topc(sK4,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_connsp_2(X0,X1) != X2
                & r1_tarski(X2,k1_connsp_2(X0,X1))
                & r2_hidden(X1,X2)
                & v4_pre_topc(X2,X0)
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(sK2,X1) != X2
              & r1_tarski(X2,k1_connsp_2(sK2,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,sK2)
              & v3_pre_topc(X2,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_connsp_2(sK2,X1) != X2
            & r1_tarski(X2,k1_connsp_2(sK2,X1))
            & r2_hidden(X1,X2)
            & v4_pre_topc(X2,sK2)
            & v3_pre_topc(X2,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( k1_connsp_2(sK2,sK3) != X2
          & r1_tarski(X2,k1_connsp_2(sK2,sK3))
          & r2_hidden(sK3,X2)
          & v4_pre_topc(X2,sK2)
          & v3_pre_topc(X2,sK2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

% (16642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f22,plain,
    ( ? [X2] :
        ( k1_connsp_2(sK2,sK3) != X2
        & r1_tarski(X2,k1_connsp_2(sK2,sK3))
        & r2_hidden(sK3,X2)
        & v4_pre_topc(X2,sK2)
        & v3_pre_topc(X2,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k1_connsp_2(sK2,sK3) != sK4
      & r1_tarski(sK4,k1_connsp_2(sK2,sK3))
      & r2_hidden(sK3,sK4)
      & v4_pre_topc(sK4,sK2)
      & v3_pre_topc(sK4,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                    & r2_hidden(X1,X2)
                    & v4_pre_topc(X2,X0)
                    & v3_pre_topc(X2,X0) )
                 => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                  & r2_hidden(X1,X2)
                  & v4_pre_topc(X2,X0)
                  & v3_pre_topc(X2,X0) )
               => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_connsp_2)).

fof(f43,plain,(
    r1_tarski(sK4,k1_connsp_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,(
    m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(sK4)) ),
    inference(backward_demodulation,[],[f116,f131])).

fof(f131,plain,(
    k1_connsp_2(sK2,sK3) = k1_setfam_1(sK6(k1_connsp_2(sK2,sK3),sK2,sK3)) ),
    inference(forward_demodulation,[],[f118,f109])).

fof(f109,plain,(
    k1_connsp_2(sK2,sK3) = k6_setfam_1(u1_struct_0(sK2),sK6(k1_connsp_2(sK2,sK3),sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f103,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ( ( ~ r2_hidden(X2,sK5(X1,X2,X3))
                | ~ v4_pre_topc(sK5(X1,X2,X3),X1)
                | ~ v3_pre_topc(sK5(X1,X2,X3),X1)
                | ~ r2_hidden(sK5(X1,X2,X3),X3) )
              & ( ( r2_hidden(X2,sK5(X1,X2,X3))
                  & v4_pre_topc(sK5(X1,X2,X3),X1)
                  & v3_pre_topc(sK5(X1,X2,X3),X1) )
                | r2_hidden(sK5(X1,X2,X3),X3) )
              & m1_subset_1(sK5(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ( k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,sK6(X0,X1,X2))
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,sK6(X0,X1,X2)) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X2,X4)
            | ~ v4_pre_topc(X4,X1)
            | ~ v3_pre_topc(X4,X1)
            | ~ r2_hidden(X4,X3) )
          & ( ( r2_hidden(X2,X4)
              & v4_pre_topc(X4,X1)
              & v3_pre_topc(X4,X1) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ r2_hidden(X2,sK5(X1,X2,X3))
          | ~ v4_pre_topc(sK5(X1,X2,X3),X1)
          | ~ v3_pre_topc(sK5(X1,X2,X3),X1)
          | ~ r2_hidden(sK5(X1,X2,X3),X3) )
        & ( ( r2_hidden(X2,sK5(X1,X2,X3))
            & v4_pre_topc(sK5(X1,X2,X3),X1)
            & v3_pre_topc(sK5(X1,X2,X3),X1) )
          | r2_hidden(sK5(X1,X2,X3),X3) )
        & m1_subset_1(sK5(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k6_setfam_1(u1_struct_0(X1),X5) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,X5)
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,X5) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( k6_setfam_1(u1_struct_0(X1),sK6(X0,X1,X2)) = X0
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK6(X0,X1,X2))
                | ~ r2_hidden(X2,X6)
                | ~ v4_pre_topc(X6,X1)
                | ~ v3_pre_topc(X6,X1) )
              & ( ( r2_hidden(X2,X6)
                  & v4_pre_topc(X6,X1)
                  & v3_pre_topc(X6,X1) )
                | ~ r2_hidden(X6,sK6(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ? [X4] :
                ( ( ~ r2_hidden(X2,X4)
                  | ~ v4_pre_topc(X4,X1)
                  | ~ v3_pre_topc(X4,X1)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X2,X4)
                    & v4_pre_topc(X4,X1)
                    & v3_pre_topc(X4,X1) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ? [X5] :
            ( k6_setfam_1(u1_struct_0(X1),X5) = X0
            & ! [X6] :
                ( ( ( r2_hidden(X6,X5)
                    | ~ r2_hidden(X2,X6)
                    | ~ v4_pre_topc(X6,X1)
                    | ~ v3_pre_topc(X6,X1) )
                  & ( ( r2_hidden(X2,X6)
                      & v4_pre_topc(X6,X1)
                      & v3_pre_topc(X6,X1) )
                    | ~ r2_hidden(X6,X5) ) )
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v4_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v4_pre_topc(X4,X0)
                    & v3_pre_topc(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v4_pre_topc(X4,X0)
                      & v3_pre_topc(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v4_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v4_pre_topc(X4,X0)
                    & v3_pre_topc(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v4_pre_topc(X4,X0)
                      & v3_pre_topc(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ? [X3] :
          ( k6_setfam_1(u1_struct_0(X0),X3) = X2
          & ! [X4] :
              ( ( r2_hidden(X4,X3)
              <=> ( r2_hidden(X1,X4)
                  & v4_pre_topc(X4,X0)
                  & v3_pre_topc(X4,X0) ) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f103,plain,(
    sP0(k1_connsp_2(sK2,sK3),sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f94,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1,k1_connsp_2(X1,X0))
      | sP0(k1_connsp_2(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_2(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f94,plain,(
    sP1(sK3,sK2,k1_connsp_2(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f90,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f18,f17])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

fof(f90,plain,(
    m1_subset_1(k1_connsp_2(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f38,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    k6_setfam_1(u1_struct_0(sK2),sK6(k1_connsp_2(sK2,sK3),sK2,sK3)) = k1_setfam_1(sK6(k1_connsp_2(sK2,sK3),sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f107,plain,(
    m1_subset_1(sK6(k1_connsp_2(sK2,sK3),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f103,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    m1_subset_1(k1_setfam_1(sK6(k1_connsp_2(sK2,sK3),sK2,sK3)),k1_zfmisc_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f115,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,(
    r1_tarski(k1_setfam_1(sK6(k1_connsp_2(sK2,sK3),sK2,sK3)),sK4) ),
    inference(unit_resulting_resolution,[],[f108,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

% (16648)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f108,plain,(
    r2_hidden(sK4,sK6(k1_connsp_2(sK2,sK3),sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f40,f39,f103,f57])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X2,X6)
      | ~ v4_pre_topc(X6,X1)
      | ~ v3_pre_topc(X6,X1)
      | r2_hidden(X6,sK6(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    v3_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    v4_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
