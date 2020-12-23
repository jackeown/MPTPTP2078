%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1177+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0Qgn0LwT9

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:12 EST 2020

% Result     : Theorem 9.21s
% Output     : Refutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :  260 (10230 expanded)
%              Number of leaves         :   44 (2932 expanded)
%              Depth                    :   41
%              Number of atoms          : 2465 (201596 expanded)
%              Number of equality atoms :  125 (1887 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t84_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( r2_xboole_0 @ C @ D )
                  <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ( ( r2_xboole_0 @ C @ D )
                    <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_orders_2])).

thf('0',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    m2_orders_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( C != D )
                   => ( ( m1_orders_2 @ C @ A @ D )
                    <=> ~ ( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_orders_1 @ X35 @ ( k1_orders_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m2_orders_2 @ X37 @ X36 @ X35 )
      | ( m1_orders_2 @ X37 @ X36 @ X38 )
      | ( m1_orders_2 @ X38 @ X36 @ X37 )
      | ( X38 = X37 )
      | ~ ( m2_orders_2 @ X38 @ X36 @ X35 )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    m2_orders_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(d15_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( B != k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ? [D: $i] :
                        ( ( C
                          = ( k3_orders_2 @ A @ B @ D ) )
                        & ( r2_hidden @ D @ B )
                        & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) )
                & ( ( B = k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ( C = k1_xboole_0 ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7 = k1_xboole_0 )
      | ( X9
        = ( k3_orders_2 @ X8 @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) ) )
      | ~ ( m1_orders_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
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
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D_2
      = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_orders_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(d14_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k3_orders_2 @ A @ B @ C )
                = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k3_orders_2 @ X5 @ X4 @ X6 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k2_orders_2 @ X5 @ ( k6_domain_1 @ ( u1_struct_0 @ X5 ) @ X6 ) ) @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d14_orders_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_C @ X0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_C @ X0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_C @ X0 )
        = ( k3_xboole_0 @ sk_C @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k3_orders_2 @ sk_A @ sk_C @ X0 )
        = ( k3_xboole_0 @ sk_C @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
      = ( k3_xboole_0 @ sk_C @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['51','66'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('68',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X28 @ X29 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('69',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','69'])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( r1_tarski @ sk_D_2 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['72'])).

thf('75',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('79',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7 = k1_xboole_0 )
      | ( X9
        = ( k3_orders_2 @ X8 @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) ) )
      | ~ ( m1_orders_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_2 )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) ) )
      | ( sk_D_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_2 )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) ) )
      | ( sk_D_2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ( sk_D_2 = k1_xboole_0 )
    | ( sk_C
      = ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_C
        = ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( sk_D_2 = k1_xboole_0 )
      | ( sk_C
        = ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(split,[status(esa)],['76'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('93',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_orders_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( sk_D_2 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['91','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( sk_D_2 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('106',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k3_orders_2 @ X5 @ X4 @ X6 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k2_orders_2 @ X5 @ ( k6_domain_1 @ ( u1_struct_0 @ X5 ) @ X6 ) ) @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d14_orders_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_D_2 @ X0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_D_2 @ X0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('114',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_2 )
      = ( k3_xboole_0 @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_D_2 @ X0 )
        = ( k3_xboole_0 @ sk_D_2 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['112','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k3_orders_2 @ sk_A @ sk_D_2 @ X0 )
        = ( k3_xboole_0 @ sk_D_2 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_D_2 = k1_xboole_0 )
      | ( ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
        = ( k3_xboole_0 @ sk_D_2 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) ) ) ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['104','119'])).

thf('121',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X28 @ X29 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('122',plain,
    ( ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) @ sk_D_2 )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( r1_tarski @ sk_C @ sk_D_2 )
      | ( sk_D_2 = k1_xboole_0 )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['90','122'])).

thf('124',plain,
    ( ( ( sk_D_2 = k1_xboole_0 )
      | ( r1_tarski @ sk_C @ sk_D_2 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['123'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('125',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_xboole_0 @ X15 @ X17 )
      | ( X15 = X17 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('126',plain,
    ( ( ( sk_D_2 = k1_xboole_0 )
      | ( sk_C = sk_D_2 )
      | ( r2_xboole_0 @ sk_C @ sk_D_2 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
   <= ~ ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['72'])).

thf('128',plain,
    ( ( ( sk_C = sk_D_2 )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t68_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B != k1_xboole_0 )
                & ( m1_orders_2 @ B @ A @ B ) )
            & ~ ( ~ ( m1_orders_2 @ B @ A @ B )
                & ( B = k1_xboole_0 ) ) ) ) ) )).

thf('130',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_orders_2 @ X33 @ X34 @ X33 )
      | ( X33 = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X34 )
      | ~ ( v5_orders_2 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v3_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t68_orders_2])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ~ ( m1_orders_2 @ sk_D_2 @ sk_A @ sk_D_2 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
      | ( sk_D_2 = k1_xboole_0 )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['128','138'])).

thf('140',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(split,[status(esa)],['76'])).

thf('141',plain,
    ( ( ( sk_D_2 = k1_xboole_0 )
      | ( sk_D_2 = k1_xboole_0 ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( sk_D_2 = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('144',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('145',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m2_orders_2 @ X13 @ X12 @ X11 )
      | ( X13 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v6_orders_2 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('146',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X12 @ X11 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,
    ( ( sk_D_2 = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('149',plain,(
    m2_orders_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v6_orders_2 @ X23 @ X21 )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    v6_orders_2 @ sk_D_2 @ sk_A ),
    inference('sup-',[status(thm)],['149','159'])).

thf('161',plain,
    ( ( v6_orders_2 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['148','160'])).

thf('162',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['147','161','162','163','164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,
    ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','168'])).

thf('170',plain,
    ( ( sk_D_2 = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('171',plain,(
    m2_orders_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_2 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_2 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['169','172'])).

thf('174',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['74','173'])).

thf('175',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['73','174'])).

thf('176',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','175'])).

thf('177',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_xboole_0 @ X15 @ X17 )
      | ( X15 = X17 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('178',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 )
    | ( sk_D_2 = sk_C )
    | ( r2_xboole_0 @ sk_D_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( r2_xboole_0 @ sk_D_2 @ sk_C )
    | ( sk_C = sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_2 )
   <= ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['76'])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('182',plain,
    ( ~ ( r2_xboole_0 @ sk_D_2 @ sk_C )
   <= ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_2 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(split,[status(esa)],['76'])).

thf('184',plain,(
    r2_xboole_0 @ sk_C @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['74','173','183'])).

thf('185',plain,(
    ~ ( r2_xboole_0 @ sk_D_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['182','184'])).

thf('186',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_2 ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( sk_C = sk_D_2 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_2 )
   <= ( r2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['76'])).

thf('190',plain,(
    r2_xboole_0 @ sk_C @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['74','173','183'])).

thf('191',plain,(
    r2_xboole_0 @ sk_C @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['188','191'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('193',plain,(
    ! [X24: $i] :
      ~ ( r2_xboole_0 @ X24 @ X24 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('194',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','194'])).

thf('196',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X12 @ X11 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('200',plain,(
    v6_orders_2 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['192','193'])).

thf('202',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','202','203','204','205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','209'])).

thf('211',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['192','193'])).

thf('213',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    $false ),
    inference(demod,[status(thm)],['210','213'])).


%------------------------------------------------------------------------------
