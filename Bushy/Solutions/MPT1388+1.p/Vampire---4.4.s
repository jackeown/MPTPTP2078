%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t13_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 (2945 expanded)
%              Number of leaves         :   16 ( 970 expanded)
%              Depth                    :   21
%              Number of atoms          :  524 (19083 expanded)
%              Number of equality atoms :   53 ( 611 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1665,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1664,f128])).

fof(f128,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f85,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',t3_subset)).

fof(f85,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ r3_connsp_1(sK0,sK2,sK1)
    & r1_tarski(sK1,sK2)
    & v3_connsp_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f58,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_connsp_1(X0,X2,X1)
                & r1_tarski(X1,X2)
                & v3_connsp_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(sK0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r3_connsp_1(X0,X2,sK1)
            & r1_tarski(sK1,X2)
            & v3_connsp_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_connsp_1(X0,X2,X1)
          & r1_tarski(X1,X2)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r3_connsp_1(X0,sK2,X1)
        & r1_tarski(X1,sK2)
        & v3_connsp_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_connsp_1(X1,X0) )
                 => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_connsp_1(X1,X0) )
                 => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_connsp_1(X1,X0) )
               => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',t13_connsp_2)).

fof(f1664,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(forward_demodulation,[],[f1660,f424])).

fof(f424,plain,(
    u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(forward_demodulation,[],[f175,f153])).

fof(f153,plain,(
    k2_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(unit_resulting_resolution,[],[f81,f83,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f104,f103,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',d10_pre_topc)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',dt_k1_pre_topc)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f175,plain,(
    u1_struct_0(k1_pre_topc(sK0,sK2)) = k2_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f172,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',d3_struct_0)).

fof(f172,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f168,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',dt_l1_pre_topc)).

fof(f168,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f81,f147,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',dt_m1_pre_topc)).

fof(f147,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f81,f83,f104])).

fof(f1660,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f168,f1508,f1594,f1648,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | v3_connsp_1(X1,X0)
      | ~ v2_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ( sK4(X0,X1) != X1
                & r1_tarski(X1,sK4(X0,X1))
                & v2_connsp_1(sK4(X0,X1),X0)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_connsp_1(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_connsp_1(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) != X1
        & r1_tarski(X1,sK4(X0,X1))
        & v2_connsp_1(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_connsp_1(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_connsp_1(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_connsp_1(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_connsp_1(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_connsp_1(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_connsp_1(X2,X0) )
                   => X1 = X2 ) )
              & v2_connsp_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',d5_connsp_1)).

fof(f1648,plain,(
    sK1 = sK4(k1_pre_topc(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f81,f84,f82,f1596,f1617,f1637,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X3)
      | ~ v2_connsp_1(X3,X0)
      | X1 = X3
      | ~ v3_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1637,plain,(
    v2_connsp_1(sK4(k1_pre_topc(sK0,sK2),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f80,f81,f147,f1616,f1635,f444])).

fof(f444,plain,(
    ! [X19,X20] :
      ( ~ v2_connsp_1(X19,k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X19,k1_zfmisc_1(sK2))
      | v2_connsp_1(X19,X20)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X20)
      | ~ l1_pre_topc(X20)
      | ~ v2_pre_topc(X20) ) ),
    inference(superposition,[],[f181,f424])).

fof(f181,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f116,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',t39_pre_topc)).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X0)
      | ~ v2_connsp_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X2,X0)
      | ~ v2_connsp_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_connsp_1(X2,X0)
                      | ~ v2_connsp_1(X3,X1) )
                    & ( v2_connsp_1(X3,X1)
                      | ~ v2_connsp_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_connsp_1(X2,X0)
                    <=> v2_connsp_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',t24_connsp_1)).

fof(f1635,plain,(
    v2_connsp_1(sK4(k1_pre_topc(sK0,sK2),sK1),k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f128,f1508,f1594,f459])).

fof(f459,plain,(
    ! [X11] :
      ( v2_connsp_1(sK4(k1_pre_topc(sK0,sK2),X11),k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X11,k1_zfmisc_1(sK2))
      | ~ v2_connsp_1(X11,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X11,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f437,f168])).

fof(f437,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(sK2))
      | v2_connsp_1(sK4(k1_pre_topc(sK0,sK2),X11),k1_pre_topc(sK0,sK2))
      | ~ v2_connsp_1(X11,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X11,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f96,f424])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_connsp_1(sK4(X0,X1),X0)
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1616,plain,(
    m1_subset_1(sK4(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f128,f1508,f1594,f458])).

fof(f458,plain,(
    ! [X10] :
      ( ~ v2_connsp_1(X10,k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X10,k1_zfmisc_1(sK2))
      | m1_subset_1(sK4(k1_pre_topc(sK0,sK2),X10),k1_zfmisc_1(sK2))
      | v3_connsp_1(X10,k1_pre_topc(sK0,sK2)) ) ),
    inference(forward_demodulation,[],[f457,f424])).

fof(f457,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(sK2))
      | m1_subset_1(sK4(k1_pre_topc(sK0,sK2),X10),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
      | ~ v2_connsp_1(X10,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X10,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f436,f168])).

fof(f436,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(sK2))
      | m1_subset_1(sK4(k1_pre_topc(sK0,sK2),X10),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
      | ~ v2_connsp_1(X10,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X10,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f95,f424])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f1617,plain,(
    m1_subset_1(sK4(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f81,f147,f1616,f441])).

fof(f441,plain,(
    ! [X15,X16] :
      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X16)
      | m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(sK2))
      | ~ l1_pre_topc(X16) ) ),
    inference(superposition,[],[f109,f424])).

fof(f1596,plain,(
    r1_tarski(sK1,sK4(k1_pre_topc(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f128,f1508,f1594,f460])).

fof(f460,plain,(
    ! [X12] :
      ( ~ v2_connsp_1(X12,k1_pre_topc(sK0,sK2))
      | r1_tarski(X12,sK4(k1_pre_topc(sK0,sK2),X12))
      | ~ m1_subset_1(X12,k1_zfmisc_1(sK2))
      | v3_connsp_1(X12,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f438,f168])).

fof(f438,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(sK2))
      | r1_tarski(X12,sK4(k1_pre_topc(sK0,sK2),X12))
      | ~ v2_connsp_1(X12,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X12,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f97,f424])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK4(X0,X1))
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f82,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    v3_connsp_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f1594,plain,(
    v2_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f80,f81,f151,f128,f147,f445])).

fof(f445,plain,(
    ! [X21,X22] :
      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X22)
      | ~ v2_connsp_1(X21,X22)
      | v2_connsp_1(X21,k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X21,k1_zfmisc_1(sK2))
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22) ) ),
    inference(superposition,[],[f186,f424])).

fof(f186,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_connsp_1(X3,X0)
      | v2_connsp_1(X3,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f117,f109])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X1)
      | ~ v2_connsp_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X3,X1)
      | ~ v2_connsp_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f151,plain,(
    v2_connsp_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f81,f84,f82,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_connsp_1(X1,X0)
      | v2_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1508,plain,(
    ~ v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f128,f86,f82,f447])).

fof(f447,plain,(
    ! [X0] :
      ( ~ v3_connsp_1(X0,k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | r3_connsp_1(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f446,f81])).

fof(f446,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ v3_connsp_1(X0,k1_pre_topc(sK0,sK2))
      | r3_connsp_1(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f430,f83])).

fof(f430,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ v3_connsp_1(X0,k1_pre_topc(sK0,sK2))
      | r3_connsp_1(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f115,f424])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
      | r3_connsp_1(X0,X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_connsp_1(X0,X1,X2)
      | ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ( v3_connsp_1(sK3(X0,X1,X2),k1_pre_topc(X0,X1))
                    & sK3(X0,X1,X2) = X2
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_connsp_1(X4,k1_pre_topc(X0,X1))
          & X2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
     => ( v3_connsp_1(sK3(X0,X1,X2),k1_pre_topc(X0,X1))
        & sK3(X0,X1,X2) = X2
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ? [X4] :
                      ( v3_connsp_1(X4,k1_pre_topc(X0,X1))
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ? [X3] :
                      ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_connsp_1(X0,X1,X2)
              <=> ? [X3] :
                    ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r3_connsp_1(X0,X1,X2)
              <=> ? [X3] :
                    ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t13_connsp_2.p',d6_connsp_1)).

fof(f86,plain,(
    ~ r3_connsp_1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
