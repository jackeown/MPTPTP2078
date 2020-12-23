%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ujy25RJdGU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 (1370 expanded)
%              Number of leaves         :   24 ( 402 expanded)
%              Depth                    :   25
%              Number of atoms          : 1176 (21774 expanded)
%              Number of equality atoms :   44 ( 192 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t67_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_orders_2 @ C @ A @ B )
               => ( r1_tarski @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_orders_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m1_orders_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_orders_2 @ X9 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
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
      ( ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X5 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( X5
        = ( k3_orders_2 @ X4 @ X3 @ ( sk_D_1 @ X5 @ X3 @ X4 ) ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
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
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_C
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['18','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( r1_tarski @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf('81',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('83',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf('93',plain,(
    m1_orders_2 @ sk_C @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('99',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('101',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf('106',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf('107',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['77','96','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ujy25RJdGU
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 89 iterations in 0.066s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.53  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.53  thf(t67_orders_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t67_orders_2])).
% 0.20/0.53  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_m1_orders_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( m1_orders_2 @ C @ A @ B ) =>
% 0.20/0.53           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (l1_orders_2 @ X7)
% 0.20/0.53          | ~ (v5_orders_2 @ X7)
% 0.20/0.53          | ~ (v4_orders_2 @ X7)
% 0.20/0.53          | ~ (v3_orders_2 @ X7)
% 0.20/0.53          | (v2_struct_0 @ X7)
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | ~ (m1_orders_2 @ X9 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_orders_2])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.53  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53           ( ( ![D:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.53                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.53             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.53          | (r1_tarski @ X2 @ X0)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.53             (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.53        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.53  thf('17', plain, (~ (r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.53        (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d15_orders_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.20/0.53                     ( ?[D:$i]:
% 0.20/0.53                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.20/0.53                         ( r2_hidden @ D @ B ) & 
% 0.20/0.53                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.20/0.53                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.20/0.53                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ((X3) = (k1_xboole_0))
% 0.20/0.53          | (m1_subset_1 @ (sk_D_1 @ X5 @ X3 @ X4) @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | ~ (v4_orders_2 @ X4)
% 0.20/0.53          | ~ (v3_orders_2 @ X4)
% 0.20/0.53          | (v2_struct_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '27'])).
% 0.20/0.53  thf('29', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ((X3) = (k1_xboole_0))
% 0.20/0.53          | ((X5) = (k3_orders_2 @ X4 @ X3 @ (sk_D_1 @ X5 @ X3 @ X4)))
% 0.20/0.53          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | ~ (v4_orders_2 @ X4)
% 0.20/0.53          | ~ (v3_orders_2 @ X4)
% 0.20/0.53          | (v2_struct_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.53          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ X0 @ sk_B @ sk_A)))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.53          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ X0 @ sk_B @ sk_A)))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.53        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '41'])).
% 0.20/0.53  thf('43', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((sk_C) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t57_orders_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.20/0.53                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.53          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 0.20/0.53          | (r2_hidden @ X10 @ X12)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.20/0.53          | ~ (l1_orders_2 @ X11)
% 0.20/0.53          | ~ (v5_orders_2 @ X11)
% 0.20/0.53          | ~ (v4_orders_2 @ X11)
% 0.20/0.53          | ~ (v3_orders_2 @ X11)
% 0.20/0.53          | (v2_struct_0 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ X1 @ sk_B)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ X1 @ sk_B)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.53          | ((sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B) = (k1_xboole_0))
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.53        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.53          | (r1_tarski @ X2 @ X0)
% 0.20/0.53          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.53          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '62'])).
% 0.20/0.53  thf('64', plain, (~ (r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((r2_hidden @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_C)),
% 0.20/0.53      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '65'])).
% 0.20/0.53  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (((r2_hidden @ (sk_D @ sk_B @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.53        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.53          | (r1_tarski @ X2 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.53          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (r1_tarski @ sk_C @ sk_B)
% 0.20/0.53        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('74', plain, ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_C @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, (~ (r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, (~ (r1_tarski @ sk_C @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('80', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ((X3) != (k1_xboole_0))
% 0.20/0.53          | ((X5) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | ~ (v4_orders_2 @ X4)
% 0.20/0.53          | ~ (v3_orders_2 @ X4)
% 0.20/0.53          | (v2_struct_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X4)
% 0.20/0.53          | ~ (v3_orders_2 @ X4)
% 0.20/0.53          | ~ (v4_orders_2 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.53          | ~ (m1_orders_2 @ X5 @ X4 @ k1_xboole_0)
% 0.20/0.53          | ((X5) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['81', '83'])).
% 0.20/0.53  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('86', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('88', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (m1_orders_2 @ sk_C @ sk_A @ k1_xboole_0)
% 0.20/0.53        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['78', '89'])).
% 0.20/0.53  thf('91', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('92', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('93', plain, ((m1_orders_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain, (((v2_struct_0 @ sk_A) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['90', '93'])).
% 0.20/0.53  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('96', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.53          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_B)
% 0.20/0.53        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.53          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_B)
% 0.20/0.53        | (r1_tarski @ sk_B @ sk_B)
% 0.20/0.53        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('103', plain, (((r1_tarski @ sk_B @ sk_B) | (r1_tarski @ sk_B @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.20/0.53      inference('simplify', [status(thm)], ['103'])).
% 0.20/0.53  thf('105', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('106', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('107', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.20/0.53  thf('108', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '96', '107'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
