%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1147+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 (11086 expanded)
%              Number of leaves         :    4 (1810 expanded)
%              Depth                    :   52
%              Number of atoms          :  700 (100049 expanded)
%              Number of equality atoms :   13 ( 362 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1022,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1021,f1011])).

fof(f1011,plain,(
    r2_orders_2(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f1010,f778])).

fof(f778,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f777,f744])).

fof(f744,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f743,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                <=> ( r2_orders_2(X0,X1,X2)
                  <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <=> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).

fof(f743,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f742,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f742,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f741,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f741,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f731])).

fof(f731,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f700,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f700,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f689,f462])).

fof(f462,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f461,f19])).

fof(f19,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f461,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f460,f25])).

fof(f460,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f459,f24])).

fof(f459,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f458,f28])).

fof(f458,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f457,f26])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f457,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f238,f18])).

fof(f18,plain,
    ( v6_orders_2(sK3,sK0)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f238,plain,(
    ! [X1] :
      ( ~ v6_orders_2(sK3,X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK2,u1_struct_0(X1))
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | r1_orders_2(sK0,sK2,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(X1,sK2,sK1)
      | r1_orders_2(X1,sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK2,u1_struct_0(X1))
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | ~ v6_orders_2(sK3,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(X1,sK2,sK1)
      | r1_orders_2(X1,sK1,sK2)
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(sK0,sK2,sK1) ) ),
    inference(resolution,[],[f139,f21])).

fof(f21,plain,
    ( r2_hidden(sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK3)
      | r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | ~ v6_orders_2(sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(X0,X1,sK1)
      | r1_orders_2(X0,sK1,X1) ) ),
    inference(resolution,[],[f20,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X4)
      | r1_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f20,plain,
    ( r2_hidden(sK1,sK3)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f689,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f688,f24])).

fof(f688,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f687,f25])).

fof(f687,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f686,f28])).

fof(f686,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f685,f26])).

fof(f685,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f684,f599])).

fof(f599,plain,(
    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f598,f24])).

fof(f598,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f597,f25])).

fof(f597,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f591,f210])).

fof(f210,plain,(
    ! [X4,X5] :
      ( ~ r2_orders_2(sK0,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X5,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f207,f28])).

fof(f207,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X5,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ r2_orders_2(sK0,X5,X4) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X5,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X5,X4) ) ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X10,X11] :
      ( ~ r1_orders_2(sK0,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X10,X11),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f49,f28])).

fof(f49,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X10,X11)
      | m1_subset_1(sK4(sK0,X10,X11),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f591,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f590,f25])).

fof(f590,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f589,f24])).

fof(f589,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f575])).

fof(f575,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f483,f54])).

fof(f483,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f482,f25])).

fof(f482,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f468,f24])).

fof(f468,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f462,f53])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X2,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f45,f28])).

fof(f45,plain,(
    ! [X2,X3] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X3,X2)
      | m1_subset_1(sK4(sK0,X2,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f684,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f681])).

fof(f681,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f603,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | v6_orders_2(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f603,plain,(
    ! [X0] :
      ( ~ v6_orders_2(sK4(X0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK4(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK1,sK2)
      | ~ r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | ~ m1_subset_1(sK2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f600])).

fof(f600,plain,(
    ! [X0] :
      ( ~ v6_orders_2(sK4(X0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK4(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK1,sK2)
      | ~ r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | ~ m1_subset_1(sK2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK2,sK1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | ~ m1_subset_1(sK2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK2,sK1) ) ),
    inference(resolution,[],[f214,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1,sK4(X0,X1,sK2))
      | ~ v6_orders_2(sK4(X0,X1,sK2),sK0)
      | ~ m1_subset_1(sK4(X0,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK1,sK2)
      | ~ r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK2,X1) ) ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | r2_hidden(X2,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | r2_orders_2(sK0,sK1,sK2)
      | ~ v6_orders_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ r1_orders_2(sK0,sK2,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f777,plain,
    ( sK1 = sK2
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f776,f24])).

fof(f776,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f760,f25])).

fof(f760,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f745,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_orders_2(sK0,X1,X0) ) ),
    inference(resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f745,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f744,f660])).

fof(f660,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f659,f24])).

fof(f659,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f658,f25])).

fof(f658,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f657,f28])).

fof(f657,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f656])).

fof(f656,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f650,f29])).

fof(f650,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f649,f24])).

fof(f649,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f648,f25])).

fof(f648,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f647,f28])).

fof(f647,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f646,f26])).

fof(f646,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f644,f599])).

fof(f644,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f643])).

fof(f643,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f395,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | v6_orders_2(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f395,plain,(
    ! [X1] :
      ( ~ v6_orders_2(sK4(X1,sK1,sK2),sK0)
      | ~ m1_subset_1(sK4(X1,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | ~ m1_subset_1(sK2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,(
    ! [X1] :
      ( ~ v6_orders_2(sK4(X1,sK1,sK2),sK0)
      | ~ m1_subset_1(sK4(X1,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | ~ m1_subset_1(sK2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK1,sK2)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | ~ m1_subset_1(sK2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK1,sK2) ) ),
    inference(resolution,[],[f172,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK1,sK4(X2,X3,sK2))
      | ~ v6_orders_2(sK4(X2,X3,sK2),sK0)
      | ~ m1_subset_1(sK4(X2,X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X2)
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(sK2,u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,sK2) ) ),
    inference(resolution,[],[f22,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(X2,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ v6_orders_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | r1_orders_2(sK0,sK2,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1010,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f857,f1009])).

fof(f1009,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f1008,f943])).

fof(f943,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f872,f778])).

fof(f872,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f811])).

fof(f811,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f245,f778])).

fof(f245,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f244,f19])).

fof(f244,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f243,f25])).

fof(f243,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f242,f28])).

fof(f242,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f241,f26])).

fof(f241,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f239,f18])).

fof(f239,plain,(
    ! [X0] :
      ( ~ v6_orders_2(sK3,X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | r1_orders_2(sK0,sK2,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(X0,sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK2,sK1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | ~ v6_orders_2(sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(X0,sK1,sK1)
      | r1_orders_2(X0,sK1,sK1)
      | r2_orders_2(sK0,sK1,sK2)
      | r1_orders_2(sK0,sK2,sK1) ) ),
    inference(resolution,[],[f139,f20])).

fof(f1008,plain,
    ( ~ r2_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f856,f778])).

fof(f856,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f660,f778])).

fof(f857,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f689,f778])).

fof(f1021,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f1018,f25])).

fof(f1018,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f1014])).

fof(f1014,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f1011,f182])).

fof(f182,plain,(
    ! [X4,X5] :
      ( ~ r2_orders_2(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X5,X4) ) ),
    inference(subsumption_resolution,[],[f181,f28])).

fof(f181,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X4,X5)
      | ~ l1_orders_2(sK0)
      | ~ r2_orders_2(sK0,X5,X4) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X4,X5)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X5,X4) ) ),
    inference(resolution,[],[f56,f29])).

%------------------------------------------------------------------------------
