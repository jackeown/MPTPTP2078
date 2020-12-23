%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  140 (1632 expanded)
%              Number of leaves         :   15 ( 608 expanded)
%              Depth                    :   52
%              Number of atoms          :  703 (21949 expanded)
%              Number of equality atoms :  100 (1563 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(subsumption_resolution,[],[f287,f41])).

fof(f41,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v5_pre_topc(sK3,sK0,sK2)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | ~ v1_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK3,sK1,sK2)
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      | ~ v5_pre_topc(X3,X0,X2)
                      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      | ~ v1_funct_1(X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v5_pre_topc(X3,X1,X2)
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                & u1_struct_0(X0) = u1_struct_0(X1)
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,sK0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK0))
              & u1_struct_0(X1) = u1_struct_0(sK0)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                  | ~ v5_pre_topc(X3,sK0,X2)
                  | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                & v5_pre_topc(X3,X1,X2)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK0))
            & u1_struct_0(X1) = u1_struct_0(sK0)
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                | ~ v5_pre_topc(X3,sK0,X2)
                | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
              & v5_pre_topc(X3,sK1,X2)
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
          & u1_struct_0(sK0) = u1_struct_0(sK1)
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
              | ~ v5_pre_topc(X3,sK0,X2)
              | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
            & v5_pre_topc(X3,sK1,X2)
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
        & u1_struct_0(sK0) = u1_struct_0(sK1)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
            | ~ v5_pre_topc(X3,sK0,sK2)
            | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v5_pre_topc(X3,sK1,sK2)
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X3) )
      & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
          | ~ v5_pre_topc(X3,sK0,sK2)
          | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
          | ~ v1_funct_1(X3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v5_pre_topc(X3,sK1,sK2)
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        | ~ v5_pre_topc(sK3,sK0,sK2)
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v5_pre_topc(sK3,sK1,sK2)
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X1,X2)
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X1,X2)
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X1,X2)
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X0,X2)
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tmap_1)).

fof(f287,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f286,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f286,plain,(
    ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f285,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f285,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK2) ),
    inference(backward_demodulation,[],[f88,f281])).

fof(f281,plain,(
    k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f280,f82])).

fof(f82,plain,(
    v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f79,f76])).

fof(f76,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f71,f41])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f50,f51])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f79,plain,(
    v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f67,f74])).

fof(f74,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f45,f42])).

fof(f42,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f280,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f279,f74])).

fof(f279,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK2))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f278,f76])).

fof(f278,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f277,f83])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f78,f76])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f68,f74])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f47,f42])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f277,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f276,f74])).

fof(f276,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK2))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f275,f76])).

fof(f275,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f274,f37])).

fof(f274,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f273,f41])).

fof(f273,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f272,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f272,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f261,f70])).

fof(f70,plain,(
    ~ v5_pre_topc(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f69,f68])).

fof(f69,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f66,f67])).

fof(f66,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f48,f44])).

fof(f48,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f261,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | v5_pre_topc(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | v5_pre_topc(sK3,sK0,sK2)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f257,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v3_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v3_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f257,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK2,sK3),sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f255,f83])).

fof(f255,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK2,sK3),sK2)
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) ),
    inference(resolution,[],[f248,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f248,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK4(sK0,sK2,sK3),sK2)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f247,f99])).

fof(f99,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f98,f76])).

fof(f98,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f97,f82])).

fof(f97,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2))
    | k1_xboole_0 = k2_struct_0(sK2)
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f96,f74])).

fof(f96,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK2))
    | k1_xboole_0 = k2_struct_0(sK2)
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f95,f76])).

fof(f95,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f94,f83])).

fof(f94,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f93,f74])).

fof(f93,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK2))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f92,f76])).

fof(f92,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f90,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f70])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK3,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | m1_subset_1(sK4(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f247,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(sK4(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(sK4(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(resolution,[],[f240,f138])).

fof(f138,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK1)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f137,f80])).

fof(f80,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f42,f74])).

fof(f137,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK1)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f136,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f136,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK1)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(resolution,[],[f135,f43])).

fof(f43,plain,(
    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK0))
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0)
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(sK2) ) ),
    inference(resolution,[],[f126,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f126,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(u1_pre_topc(sK0)))
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X2)
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f124,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) ) ),
    inference(subsumption_resolution,[],[f122,f83])).

% (26851)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(sK2)
      | ~ r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) ) ),
    inference(resolution,[],[f121,f65])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f119,plain,
    ( ~ r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),u1_pre_topc(sK0))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f118,f74])).

fof(f118,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),u1_pre_topc(sK0))
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f117,f37])).

fof(f117,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),u1_pre_topc(sK0))
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f115,f74])).

fof(f115,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)
    | k1_xboole_0 = k2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f114,f76])).

fof(f114,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(subsumption_resolution,[],[f113,f82])).

fof(f113,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(forward_demodulation,[],[f112,f74])).

fof(f112,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK2))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(forward_demodulation,[],[f111,f76])).

fof(f111,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(subsumption_resolution,[],[f110,f83])).

fof(f110,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(forward_demodulation,[],[f109,f74])).

fof(f109,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK2))))
    | k1_xboole_0 = k2_struct_0(sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(forward_demodulation,[],[f108,f76])).

fof(f108,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f107,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f106,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f105,f70])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK3,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK4(X0,X1,sK3)),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f240,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f239,f39])).

fof(f239,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f238,f46])).

fof(f46,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f238,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f237,f83])).

fof(f237,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f234,f82])).

fof(f234,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f197,f80])).

fof(f197,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(sK3,u1_struct_0(X5),k2_struct_0(sK2))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X5),k2_struct_0(sK2),sK3,X4),X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK2))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,X5,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v3_pre_topc(X4,sK2)
      | ~ l1_pre_topc(X5) ) ),
    inference(forward_demodulation,[],[f196,f76])).

fof(f196,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(sK3,u1_struct_0(X5),k2_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK2))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,X5,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5)
      | ~ v3_pre_topc(X4,sK2)
      | ~ l1_pre_topc(X5) ) ),
    inference(forward_demodulation,[],[f195,f76])).

fof(f195,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK2))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,X5,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ v1_funct_2(sK3,u1_struct_0(X5),u1_struct_0(sK2))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5)
      | ~ v3_pre_topc(X4,sK2)
      | ~ l1_pre_topc(X5) ) ),
    inference(forward_demodulation,[],[f194,f76])).

fof(f194,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,X5,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X5),u1_struct_0(sK2))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5)
      | ~ v3_pre_topc(X4,sK2)
      | ~ l1_pre_topc(X5) ) ),
    inference(forward_demodulation,[],[f184,f76])).

fof(f184,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,X5,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X5),u1_struct_0(sK2))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5)
      | ~ v3_pre_topc(X4,sK2)
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f181,f41])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(sK3,X2,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK3,X0),X2)
      | ~ v3_pre_topc(X0,X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f62,f76])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (26855)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.46  % (26863)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.48  % (26847)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.48  % (26847)Refutation not found, incomplete strategy% (26847)------------------------------
% 0.22/0.48  % (26847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26845)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (26847)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26847)Memory used [KB]: 10618
% 0.22/0.49  % (26847)Time elapsed: 0.067 s
% 0.22/0.49  % (26847)------------------------------
% 0.22/0.49  % (26847)------------------------------
% 0.22/0.50  % (26844)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (26852)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (26863)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f287,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    l1_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ((((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) & u1_struct_0(sK0) = u1_struct_0(sK1) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK0)) & u1_struct_0(X1) = u1_struct_0(sK0) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK0)) & u1_struct_0(X1) = u1_struct_0(sK0) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) & v5_pre_topc(X3,sK1,X2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) & u1_struct_0(sK0) = u1_struct_0(sK1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) & v5_pre_topc(X3,sK1,X2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) & u1_struct_0(sK0) = u1_struct_0(sK1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(X3,sK0,sK2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X3,sK1,sK2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) & u1_struct_0(sK0) = u1_struct_0(sK1) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(X3,sK0,sK2) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X3,sK1,sK2) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3))) & (r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1))) & (l1_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tmap_1)).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(resolution,[],[f286,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    ~l1_struct_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f285,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK2)),
% 0.22/0.50    inference(backward_demodulation,[],[f88,f281])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f280,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f79,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f71,f41])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f50,f51])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    v1_funct_2(sK3,k2_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f67,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f71,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f45,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2)) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f279,f74])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK2)) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f278,f76])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f277,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))),
% 0.22/0.50    inference(backward_demodulation,[],[f78,f76])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK2))))),
% 0.22/0.50    inference(backward_demodulation,[],[f68,f74])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))),
% 0.22/0.50    inference(backward_demodulation,[],[f47,f42])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f276,f74])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK2)))) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f275,f76])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f274,f37])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f273,f41])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f272,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f261,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f69,f68])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f67])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f48,f44])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK0,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | v5_pre_topc(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f259])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | v5_pre_topc(sK3,sK0,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(resolution,[],[f257,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~v3_pre_topc(sK4(sK0,sK2,sK3),sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f255,f83])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    ~v3_pre_topc(sK4(sK0,sK2,sK3),sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))),
% 0.22/0.50    inference(resolution,[],[f248,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(sK4(sK0,sK2,sK3),sK2) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f247,f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f98,f76])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f97,f82])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2)) | k1_xboole_0 = k2_struct_0(sK2) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(forward_demodulation,[],[f96,f74])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK2)) | k1_xboole_0 = k2_struct_0(sK2) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(forward_demodulation,[],[f95,f76])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f94,f83])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(forward_demodulation,[],[f93,f74])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK2)))) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(forward_demodulation,[],[f92,f76])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f91,f37])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f90,f41])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(resolution,[],[f89,f70])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v5_pre_topc(sK3,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | m1_subset_1(sK4(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(resolution,[],[f54,f44])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(sK4(sK0,sK2,sK3),sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f242])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(sK4(sK0,sK2,sK3),sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f240,f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK1) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f137,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK0)),
% 0.22/0.50    inference(backward_demodulation,[],[f42,f74])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK1) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f136,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    l1_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK1) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f135,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK0)) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f126,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(u1_pre_topc(sK0))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(resolution,[],[f124,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0) | k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f122,f83])).
% 0.22/0.50  % (26851)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK2) | ~r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2))))) )),
% 0.22/0.50    inference(resolution,[],[f121,f65])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK2) | ~r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f119,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),u1_pre_topc(sK0)) | k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(forward_demodulation,[],[f118,f74])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),u1_pre_topc(sK0)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f37])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~r2_hidden(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),u1_pre_topc(sK0)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(resolution,[],[f116,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f115,f74])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) | k1_xboole_0 = k2_struct_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f114,f76])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f113,f82])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2)) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f112,f74])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,u1_struct_0(sK0),k2_struct_0(sK2)) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f111,f76])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f83])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f109,f74])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK2)))) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f108,f76])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f37])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f41])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4(sK0,sK2,sK3)),sK0) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.50    inference(resolution,[],[f105,f70])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v5_pre_topc(sK3,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK4(X0,X1,sK3)),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(resolution,[],[f58,f44])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f239,f39])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | ~l1_pre_topc(sK1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f238,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v5_pre_topc(sK3,sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,sK1,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | ~l1_pre_topc(sK1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f237,f83])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,sK1,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | ~l1_pre_topc(sK1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f234,f82])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,k2_struct_0(sK0),k2_struct_0(sK2)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK2),sK3,X0),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK2)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,sK1,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X0,sK2) | ~l1_pre_topc(sK1)) )),
% 0.22/0.50    inference(superposition,[],[f197,f80])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~v1_funct_2(sK3,u1_struct_0(X5),k2_struct_0(sK2)) | v3_pre_topc(k8_relset_1(u1_struct_0(X5),k2_struct_0(sK2),sK3,X4),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,X5,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v3_pre_topc(X4,sK2) | ~l1_pre_topc(X5)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f196,f76])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~v1_funct_2(sK3,u1_struct_0(X5),k2_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,X5,sK2) | k1_xboole_0 = k2_struct_0(sK2) | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5) | ~v3_pre_topc(X4,sK2) | ~l1_pre_topc(X5)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f195,f76])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,X5,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~v1_funct_2(sK3,u1_struct_0(X5),u1_struct_0(sK2)) | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5) | ~v3_pre_topc(X4,sK2) | ~l1_pre_topc(X5)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f194,f76])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_pre_topc(sK3,X5,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X5),u1_struct_0(sK2)) | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5) | ~v3_pre_topc(X4,sK2) | ~l1_pre_topc(X5)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f184,f76])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v5_pre_topc(sK3,X5,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X5),u1_struct_0(sK2)) | v3_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK2),sK3,X4),X5) | ~v3_pre_topc(X4,sK2) | ~l1_pre_topc(X5)) )),
% 0.22/0.50    inference(resolution,[],[f181,f41])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(sK3,X2,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK3,X0),X2) | ~v3_pre_topc(X0,X1) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(resolution,[],[f52,f44])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ~v2_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.22/0.50    inference(superposition,[],[f62,f76])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (26863)------------------------------
% 0.22/0.50  % (26863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26863)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (26863)Memory used [KB]: 6396
% 0.22/0.50  % (26863)Time elapsed: 0.082 s
% 0.22/0.50  % (26863)------------------------------
% 0.22/0.50  % (26863)------------------------------
% 0.22/0.50  % (26843)Success in time 0.147 s
%------------------------------------------------------------------------------
