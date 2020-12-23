%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9VsXq9QzLi

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:38 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  327 (1893 expanded)
%              Number of leaves         :   42 ( 562 expanded)
%              Depth                    :   29
%              Number of atoms          : 3173 (50208 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(v2_waybel_1_type,type,(
    v2_waybel_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_waybel_0_type,type,(
    k6_waybel_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t28_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ~ ( r2_hidden @ C @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v1_waybel_0 @ D @ A )
                        & ( v12_waybel_0 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( v1_waybel_7 @ D @ A )
                          & ( r1_tarski @ B @ D )
                          & ~ ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v2_waybel_1 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_waybel_0 @ B @ A )
              & ( v12_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ~ ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( v1_waybel_0 @ D @ A )
                          & ( v12_waybel_0 @ D @ A )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( v1_waybel_7 @ D @ A )
                            & ( r1_tarski @ B @ D )
                            & ~ ( r2_hidden @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_waybel_7])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ A @ B ) )
        & ( v2_waybel_0 @ ( k6_waybel_0 @ A @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_xboole_0 @ ( k6_waybel_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_waybel_0])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('8',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k6_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( k6_waybel_0 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_waybel_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('18',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( v2_waybel_0 @ C @ A )
                & ( v13_waybel_0 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ( r1_subset_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v1_waybel_0 @ D @ A )
                        & ( v12_waybel_0 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( v1_waybel_7 @ D @ A )
                          & ( r1_tarski @ B @ D )
                          & ( r1_subset_1 @ D @ C ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X24 @ X22 @ X23 ) )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27','28','29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','42','43','44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( m1_subset_1 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k6_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ B @ C ) ) ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X21 @ ( k6_waybel_0 @ X20 @ X19 ) )
      | ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_2 @ ( sk_C_1 @ X0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C_2 @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) )
    | ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_2 @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('63',plain,
    ( ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C_2 @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ D @ C ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r2_hidden @ X3 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_C_1 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) @ sk_B )
    | ( r2_hidden @ sk_C_2 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) @ sk_B )
    | ( r2_hidden @ sk_C_2 @ sk_B )
    | ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_B )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) @ sk_B )
    | ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( r2_hidden @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('79',plain,(
    r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('82',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    r1_xboole_0 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( r1_subset_1 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('88',plain,
    ( ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc13_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v13_waybel_0 @ ( k6_waybel_0 @ A @ B ) @ A ) ) )).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( v13_waybel_0 @ ( k6_waybel_0 @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc13_waybel_0])).

thf('95',plain,
    ( ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('100',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v2_waybel_0 @ ( k6_waybel_0 @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_waybel_0])).

thf('103',plain,
    ( ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('108',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['47','92','100','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('113',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X32: $i] :
      ( ( r2_hidden @ sk_C_2 @ X32 )
      | ~ ( r1_tarski @ sk_B @ X32 )
      | ~ ( v1_waybel_7 @ X32 @ sk_A )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v12_waybel_0 @ X32 @ sk_A )
      | ~ ( v1_waybel_0 @ X32 @ sk_A )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v12_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_waybel_7 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_waybel_7 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('132',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('133',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('134',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_waybel_7 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_waybel_7 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('138',plain,(
    v1_waybel_7 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ X22 @ ( sk_D_1 @ X24 @ X22 @ X23 ) )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146','147','148','149','150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ sk_B @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['139','152'])).

thf('154',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('155',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('156',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ sk_B @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('158',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ sk_B @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('162',plain,(
    r1_tarski @ sk_B @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v12_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_C_2 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','138','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171','172','173','174','175','176'])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v12_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['164','177'])).

thf('179',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('180',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('181',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('182',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v12_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['178','179','180','181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v12_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('186',plain,(
    v12_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_C_2 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','186'])).

thf('188',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('189',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_subset_1 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( r1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( r1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194','195','196','197','198','199','200'])).

thf('202',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['188','201'])).

thf('203',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('204',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('205',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('207',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( r1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('211',plain,(
    r1_subset_1 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('213',plain,
    ( ( r1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('215',plain,
    ( ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ( r1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('217',plain,
    ( ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ X21 @ ( k6_waybel_0 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 )
    | ( r2_hidden @ sk_C_2 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['218','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('227',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r3_orders_2 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    r3_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['225','233'])).

thf('235',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('236',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( r3_orders_2 @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C_2 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C_2 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['234','240'])).

thf('242',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('245',plain,(
    r1_orders_2 @ sk_A @ sk_C_2 @ sk_C_2 ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['224','245'])).

thf('247',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('248',plain,(
    r2_hidden @ sk_C_2 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ X0 )
      | ~ ( r2_hidden @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,
    ( ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_2 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','250'])).

thf('252',plain,
    ( ~ ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['187','251'])).

thf('253',plain,(
    m1_subset_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('254',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_waybel_0 @ X22 @ X23 )
      | ~ ( v12_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( r1_subset_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X23 )
      | ~ ( v2_waybel_0 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v2_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ sk_A )
      | ~ ( v13_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_B @ X0 )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['256','257','258','259','260','261','262','263','264','265'])).

thf('267',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ~ ( v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['253','266'])).

thf('268',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('269',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('270',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('271',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['267','268','269','270'])).

thf('272',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) )
    | ( v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,(
    ~ ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('275',plain,(
    v1_waybel_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,(
    v1_xboole_0 @ ( sk_D_1 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['252','275'])).

thf('277',plain,(
    r1_subset_1 @ sk_B @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('278',plain,(
    v13_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('279',plain,(
    v2_waybel_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('280',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['32','276','277','278','279'])).

thf('281',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_xboole_0 @ ( k6_waybel_0 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['280','281'])).

thf('283',plain,(
    $false ),
    inference(demod,[status(thm)],['11','282'])).


%------------------------------------------------------------------------------
