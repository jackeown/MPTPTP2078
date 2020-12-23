%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1990+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MHirhilYZD

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:39 EST 2020

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  300 (2727 expanded)
%              Number of leaves         :   62 ( 869 expanded)
%              Depth                    :   26
%              Number of atoms          : 2708 (77004 expanded)
%              Number of equality atoms :   18 ( 121 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_waybel_3_type,type,(
    r1_waybel_3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_0_waybel_3_type,type,(
    a_2_0_waybel_3: $i > $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v3_waybel_3_type,type,(
    v3_waybel_3: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v24_waybel_0_type,type,(
    v24_waybel_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v2_waybel_3_type,type,(
    v2_waybel_3: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_waybel_3_type,type,(
    k1_waybel_3: $i > $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t39_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v4_waybel_7 @ B @ A )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v1_finset_1 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ( r1_waybel_3 @ A @ ( k2_yellow_0 @ A @ C ) @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ( r3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_waybel_3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v4_waybel_7 @ B @ A )
             => ! [C: $i] :
                  ( ( ~ ( v1_xboole_0 @ C )
                    & ( v1_finset_1 @ C )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ~ ( ( r1_waybel_3 @ A @ ( k2_yellow_0 @ A @ C ) @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                         => ~ ( ( r2_hidden @ D @ C )
                              & ( r3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_waybel_7])).

thf('0',plain,(
    r1_waybel_3 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(fraenkel_a_2_0_waybel_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_waybel_3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r1_waybel_3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X17 @ ( a_2_0_waybel_3 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( X17 != X18 )
      | ~ ( r1_waybel_3 @ X15 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_waybel_3])).

thf('3',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r1_waybel_3 @ X15 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X18 @ ( a_2_0_waybel_3 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k2_yellow_0 @ X0 @ X1 ) @ ( a_2_0_waybel_3 @ X0 @ X2 ) )
      | ~ ( r1_waybel_3 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_waybel_3 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k2_yellow_0 @ X0 @ X1 ) @ ( a_2_0_waybel_3 @ X0 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('13',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v4_waybel_7 @ B @ A )
          <=> ? [C: $i] :
                ( ( B
                  = ( k1_yellow_0 @ A @ C ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                & ( v1_waybel_7 @ C @ A )
                & ( v12_waybel_0 @ C @ A )
                & ( v1_waybel_0 @ C @ A )
                & ~ ( v1_xboole_0 @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v4_waybel_7 @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v2_lattice3 @ X5 )
      | ~ ( v1_lattice3 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('20',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_waybel_7 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_waybel_7 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27'])).

thf(t1_waybel_5,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( v24_waybel_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v3_waybel_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ~ ( v1_xboole_0 @ ( k1_waybel_3 @ A @ B ) )
              & ( v1_waybel_0 @ ( k1_waybel_3 @ A @ B ) @ A )
              & ( v12_waybel_0 @ ( k1_waybel_3 @ A @ B ) @ A )
              & ( m1_subset_1 @ ( k1_waybel_3 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
              & ( r3_orders_2 @ A @ B @ ( k1_yellow_0 @ A @ ( k1_waybel_3 @ A @ B ) ) )
              & ! [C: $i] :
                  ( ( ~ ( v1_xboole_0 @ C )
                    & ( v1_waybel_0 @ C @ A )
                    & ( v12_waybel_0 @ C @ A )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ( r3_orders_2 @ A @ B @ ( k1_yellow_0 @ A @ C ) )
                   => ( r1_tarski @ ( k1_waybel_3 @ A @ B ) @ C ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v3_waybel_3 @ X29 )
      | ~ ( r3_orders_2 @ X29 @ X30 @ ( k1_yellow_0 @ X29 @ X31 ) )
      | ( r1_tarski @ ( k1_waybel_3 @ X29 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v12_waybel_0 @ X31 @ X29 )
      | ~ ( v1_waybel_0 @ X31 @ X29 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v24_waybel_0 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_waybel_5])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( k1_waybel_3 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( r3_orders_2 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) )
      | ~ ( v3_waybel_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_waybel_3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v3_waybel_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v24_waybel_0 @ A )
          & ( v2_waybel_3 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v3_waybel_3 @ X1 )
      | ( v24_waybel_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_waybel_3])).

thf('37',plain,
    ( ( v24_waybel_0 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v24_waybel_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('42',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v4_waybel_7 @ X4 @ X5 )
      | ( v1_waybel_0 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v2_lattice3 @ X5 )
      | ~ ( v1_lattice3 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('46',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v4_waybel_7 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_waybel_7 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v4_waybel_7 @ X4 @ X5 )
      | ( v12_waybel_0 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v2_lattice3 @ X5 )
      | ~ ( v1_lattice3 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('57',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v4_waybel_7 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_waybel_7 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v4_waybel_7 @ X4 @ X5 )
      | ( X4
        = ( k1_yellow_0 @ X5 @ ( sk_C @ X4 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v2_lattice3 @ X5 )
      | ~ ( v1_lattice3 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('68',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B_2
      = ( k1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) )
    | ~ ( v4_waybel_7 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v4_waybel_7 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_B_2
    = ( k1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74','75'])).

thf('77',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( r1_tarski @ ( k1_waybel_3 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( r3_orders_2 @ sk_A @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','42','43','54','65','76','77'])).

thf('79',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B_2 @ sk_B_2 )
    | ( r1_tarski @ ( k1_waybel_3 @ sk_A @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r3_orders_2 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B_2 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    r3_orders_2 @ sk_A @ sk_B_2 @ sk_B_2 ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_waybel_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k1_waybel_3 @ A @ B )
            = ( a_2_0_waybel_3 @ A @ B ) ) ) ) )).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( ( k1_waybel_3 @ X3 @ X2 )
        = ( a_2_0_waybel_3 @ X3 @ X2 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_3])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_waybel_3 @ sk_A @ sk_B_2 )
      = ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_waybel_3 @ sk_A @ sk_B_2 )
      = ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('97',plain,
    ( ( k1_waybel_3 @ sk_A @ sk_B_2 )
    = ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_tarski @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','89','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v4_waybel_7 @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ ( sk_C @ X4 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v2_lattice3 @ X5 )
      | ~ ( v1_lattice3 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('101',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ~ ( v4_waybel_7 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v4_waybel_7 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('110',plain,(
    r1_tarski @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['98','109'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('111',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    m1_subset_1 @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('113',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ( m1_subset_1 @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_3 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','114'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('116',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('119',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27'])).

thf(t16_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_waybel_7 @ B @ A )
          <=> ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v1_finset_1 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ( r2_hidden @ ( k2_yellow_0 @ A @ C ) @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_waybel_0 @ X25 @ X26 )
      | ~ ( v12_waybel_0 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_waybel_7 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_D_2 @ X28 @ X25 @ X26 ) @ X25 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X26 @ X28 ) @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_finset_1 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v2_lattice3 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t16_waybel_7])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v4_waybel_7 @ X4 @ X5 )
      | ( v1_waybel_7 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v2_lattice3 @ X5 )
      | ~ ( v1_lattice3 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('130',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v4_waybel_7 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v4_waybel_7 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137'])).

thf('139',plain,(
    v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63','64'])).

thf('140',plain,(
    v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','138','139','140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_C_3 )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['119','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_finset_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('147',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('151',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27'])).

thf('152',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_waybel_0 @ X25 @ X26 )
      | ~ ( v12_waybel_0 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_waybel_7 @ X25 @ X26 )
      | ( m1_subset_1 @ ( sk_D_2 @ X28 @ X25 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X26 @ X28 ) @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_finset_1 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v2_lattice3 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t16_waybel_7])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137'])).

thf('160',plain,(
    v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63','64'])).

thf('161',plain,(
    v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158','159','160','161'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_C_3 )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['150','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_finset_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('172',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_orders_2 @ X8 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_B_2 )
    | ~ ( r2_lattice3 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['149','176'])).

thf('178',plain,
    ( sk_B_2
    = ( k1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74','75'])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('179',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X46 ) )
      | ( X45
       != ( k1_yellow_0 @ X46 @ X47 ) )
      | ~ ( r1_yellow_0 @ X46 @ X47 )
      | ( r2_lattice3 @ X46 @ X47 @ X45 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('180',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v5_orders_2 @ X46 )
      | ~ ( l1_orders_2 @ X46 )
      | ( r2_lattice3 @ X46 @ X47 @ ( k1_yellow_0 @ X46 @ X47 ) )
      | ~ ( r1_yellow_0 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','180'])).

thf('182',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27'])).

thf(t75_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v24_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( r1_yellow_0 @ A @ B ) ) ) ) )).

thf('184',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v24_waybel_0 @ X56 )
      | ( r1_yellow_0 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v1_waybel_0 @ X57 @ X56 )
      | ( v1_xboole_0 @ X57 )
      | ~ ( l1_orders_2 @ X56 )
      | ~ ( v5_orders_2 @ X56 )
      | ~ ( v3_orders_2 @ X56 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t75_waybel_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ~ ( v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('190',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['40','41'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('193',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('195',plain,(
    r1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,
    ( sk_B_2
    = ( k1_yellow_0 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74','75'])).

thf('197',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    r2_lattice3 @ sk_A @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['181','182','195','196','197','198'])).

thf('200',plain,(
    r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['177','199'])).

thf('201',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['168','169'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('202',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( r3_orders_2 @ X20 @ X19 @ X21 )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['200','206'])).

thf('208',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('211',plain,(
    r3_orders_2 @ sk_A @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X60: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ X60 @ sk_B_2 )
      | ~ ( r2_hidden @ X60 @ sk_C_3 )
      | ~ ( m1_subset_1 @ X60 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('215',plain,(
    r2_hidden @ ( k2_yellow_0 @ sk_A @ sk_C_3 ) @ ( sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('216',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27'])).

thf('217',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_waybel_0 @ X25 @ X26 )
      | ~ ( v12_waybel_0 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_waybel_7 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_D_2 @ X28 @ X25 @ X26 ) @ X28 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X26 @ X28 ) @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_finset_1 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v2_lattice3 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t16_waybel_7])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ~ ( v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_waybel_7 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137'])).

thf('225',plain,(
    v12_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63','64'])).

thf('226',plain,(
    v1_waybel_0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ X0 )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['218','219','220','221','222','223','224','225','226'])).

thf('228',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_C_3 )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_C_3 )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['215','227'])).

thf('229',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_finset_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_C_3 )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('233',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_C_3 ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_3 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_C_3 ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    $false ),
    inference(demod,[status(thm)],['213','214','235'])).


%------------------------------------------------------------------------------
