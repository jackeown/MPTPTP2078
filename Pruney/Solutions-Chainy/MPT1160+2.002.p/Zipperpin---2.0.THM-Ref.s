%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uIfDU4Vrww

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:59 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  121 (1134 expanded)
%              Number of leaves         :   35 ( 357 expanded)
%              Depth                    :   22
%              Number of atoms          :  947 (14501 expanded)
%              Number of equality atoms :   22 ( 549 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(t60_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X24 @ X23 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ X10 )
      | ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('14',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X19: $i] :
      ( ( ( k1_struct_0 @ X19 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('16',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ X27 @ ( k3_orders_2 @ X28 @ X29 @ X30 ) )
      | ( r2_hidden @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('29',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','31','32','33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','46'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X6 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    v1_xboole_0 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,
    ( ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['39','53'])).

thf('55',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ X27 @ ( k3_orders_2 @ X28 @ X29 @ X30 ) )
      | ( r2_orders_2 @ X28 @ X27 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_orders_2 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_orders_2 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_orders_2 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_orders_2 @ X21 @ X20 @ X22 )
      | ( X20 != X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( r2_orders_2 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('76',plain,
    ( ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('77',plain,(
    ~ ( r2_orders_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uIfDU4Vrww
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.81/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.02  % Solved by: fo/fo7.sh
% 0.81/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.02  % done 1144 iterations in 0.567s
% 0.81/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.02  % SZS output start Refutation
% 0.81/1.02  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.81/1.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.02  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.81/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.81/1.02  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.81/1.02  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.81/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.02  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.81/1.02  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.81/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.81/1.02  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.81/1.02  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.81/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.02  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.81/1.02  thf(t60_orders_2, conjecture,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.81/1.02         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.81/1.02       ( ![B:$i]:
% 0.81/1.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.81/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.02    (~( ![A:$i]:
% 0.81/1.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.81/1.02            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.81/1.02          ( ![B:$i]:
% 0.81/1.02            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.81/1.02    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.81/1.02  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf(t4_subset_1, axiom,
% 0.81/1.02    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.81/1.02  thf('2', plain,
% 0.81/1.02      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.81/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.81/1.02  thf(dt_k3_orders_2, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.81/1.02         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.81/1.02         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.81/1.02         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.02       ( m1_subset_1 @
% 0.81/1.02         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.81/1.02  thf('3', plain,
% 0.81/1.02      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.81/1.02          | ~ (l1_orders_2 @ X24)
% 0.81/1.02          | ~ (v5_orders_2 @ X24)
% 0.81/1.02          | ~ (v4_orders_2 @ X24)
% 0.81/1.02          | ~ (v3_orders_2 @ X24)
% 0.81/1.02          | (v2_struct_0 @ X24)
% 0.81/1.02          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.81/1.02          | (m1_subset_1 @ (k3_orders_2 @ X24 @ X23 @ X25) @ 
% 0.81/1.02             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.81/1.02      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.81/1.02  thf('4', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.81/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.81/1.02          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.81/1.02          | (v2_struct_0 @ X0)
% 0.81/1.02          | ~ (v3_orders_2 @ X0)
% 0.81/1.02          | ~ (v4_orders_2 @ X0)
% 0.81/1.02          | ~ (v5_orders_2 @ X0)
% 0.81/1.02          | ~ (l1_orders_2 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['2', '3'])).
% 0.81/1.02  thf('5', plain,
% 0.81/1.02      ((~ (l1_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v5_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v4_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v3_orders_2 @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['1', '4'])).
% 0.81/1.02  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('10', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.81/1.02      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.81/1.02  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('12', plain,
% 0.81/1.02      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('clc', [status(thm)], ['10', '11'])).
% 0.81/1.02  thf(t10_subset_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.02       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.81/1.02            ( ![C:$i]:
% 0.81/1.02              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.81/1.02  thf('13', plain,
% 0.81/1.02      (![X10 : $i, X11 : $i]:
% 0.81/1.02         ((r2_hidden @ (sk_C @ X10 @ X11) @ X10)
% 0.81/1.02          | ((X10) = (k1_xboole_0))
% 0.81/1.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.81/1.02  thf('14', plain,
% 0.81/1.02      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.81/1.02        | (r2_hidden @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02           (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.81/1.02  thf(d2_struct_0, axiom,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.81/1.02  thf('15', plain,
% 0.81/1.02      (![X19 : $i]:
% 0.81/1.02         (((k1_struct_0 @ X19) = (k1_xboole_0)) | ~ (l1_struct_0 @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.81/1.02  thf('16', plain,
% 0.81/1.02      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('17', plain,
% 0.81/1.02      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))
% 0.81/1.02        | ~ (l1_struct_0 @ sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['15', '16'])).
% 0.81/1.02  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf(dt_l1_orders_2, axiom,
% 0.81/1.02    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.81/1.02  thf('19', plain,
% 0.81/1.02      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_orders_2 @ X26))),
% 0.81/1.02      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.81/1.02  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.81/1.02      inference('sup-', [status(thm)], ['18', '19'])).
% 0.81/1.02  thf('21', plain,
% 0.81/1.02      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['17', '20'])).
% 0.81/1.02  thf('22', plain,
% 0.81/1.02      ((r2_hidden @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02        (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['14', '21'])).
% 0.81/1.02  thf('23', plain,
% 0.81/1.02      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.81/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.81/1.02  thf(t57_orders_2, axiom,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.81/1.02         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.81/1.02       ( ![B:$i]:
% 0.81/1.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02           ( ![C:$i]:
% 0.81/1.02             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02               ( ![D:$i]:
% 0.81/1.02                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/1.02                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.81/1.02                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.81/1.02  thf('24', plain,
% 0.81/1.02      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.81/1.02          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.81/1.02          | ~ (r2_hidden @ X27 @ (k3_orders_2 @ X28 @ X29 @ X30))
% 0.81/1.02          | (r2_hidden @ X27 @ X29)
% 0.81/1.02          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.81/1.02          | ~ (l1_orders_2 @ X28)
% 0.81/1.02          | ~ (v5_orders_2 @ X28)
% 0.81/1.02          | ~ (v4_orders_2 @ X28)
% 0.81/1.02          | ~ (v3_orders_2 @ X28)
% 0.81/1.02          | (v2_struct_0 @ X28))),
% 0.81/1.02      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.81/1.02  thf('25', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         ((v2_struct_0 @ X0)
% 0.81/1.02          | ~ (v3_orders_2 @ X0)
% 0.81/1.02          | ~ (v4_orders_2 @ X0)
% 0.81/1.02          | ~ (v5_orders_2 @ X0)
% 0.81/1.02          | ~ (l1_orders_2 @ X0)
% 0.81/1.02          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.81/1.02          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.81/1.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['23', '24'])).
% 0.81/1.02  thf('26', plain,
% 0.81/1.02      ((~ (m1_subset_1 @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02           (u1_struct_0 @ sk_A))
% 0.81/1.02        | (r2_hidden @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02           k1_xboole_0)
% 0.81/1.02        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.81/1.02        | ~ (l1_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v5_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v4_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v3_orders_2 @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['22', '25'])).
% 0.81/1.02  thf('27', plain,
% 0.81/1.02      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('clc', [status(thm)], ['10', '11'])).
% 0.81/1.02  thf('28', plain,
% 0.81/1.02      (![X10 : $i, X11 : $i]:
% 0.81/1.02         ((m1_subset_1 @ (sk_C @ X10 @ X11) @ X11)
% 0.81/1.02          | ((X10) = (k1_xboole_0))
% 0.81/1.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.81/1.02  thf('29', plain,
% 0.81/1.02      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.81/1.02        | (m1_subset_1 @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02           (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['27', '28'])).
% 0.81/1.02  thf('30', plain,
% 0.81/1.02      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['17', '20'])).
% 0.81/1.02  thf('31', plain,
% 0.81/1.02      ((m1_subset_1 @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02        (u1_struct_0 @ sk_A))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.81/1.02  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('35', plain, ((v4_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('37', plain,
% 0.81/1.02      (((r2_hidden @ 
% 0.81/1.02         (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02          (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02         k1_xboole_0)
% 0.81/1.02        | (v2_struct_0 @ sk_A))),
% 0.81/1.02      inference('demod', [status(thm)],
% 0.81/1.02                ['26', '31', '32', '33', '34', '35', '36'])).
% 0.81/1.02  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('39', plain,
% 0.81/1.02      ((r2_hidden @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02        k1_xboole_0)),
% 0.81/1.02      inference('clc', [status(thm)], ['37', '38'])).
% 0.81/1.02  thf('40', plain,
% 0.81/1.02      ((r2_hidden @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02        k1_xboole_0)),
% 0.81/1.02      inference('clc', [status(thm)], ['37', '38'])).
% 0.81/1.02  thf(d10_xboole_0, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.02  thf('41', plain,
% 0.81/1.02      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.81/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.02  thf('42', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.81/1.02      inference('simplify', [status(thm)], ['41'])).
% 0.81/1.02  thf(t3_subset, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/1.02  thf('43', plain,
% 0.81/1.02      (![X13 : $i, X15 : $i]:
% 0.81/1.02         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.81/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.02  thf('44', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['42', '43'])).
% 0.81/1.02  thf(t4_subset, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.81/1.02       ( m1_subset_1 @ A @ C ) ))).
% 0.81/1.02  thf('45', plain,
% 0.81/1.02      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X16 @ X17)
% 0.81/1.02          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.81/1.02          | (m1_subset_1 @ X16 @ X18))),
% 0.81/1.02      inference('cnf', [status(esa)], [t4_subset])).
% 0.81/1.02  thf('46', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['44', '45'])).
% 0.81/1.02  thf('47', plain,
% 0.81/1.02      ((m1_subset_1 @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02        k1_xboole_0)),
% 0.81/1.02      inference('sup-', [status(thm)], ['40', '46'])).
% 0.81/1.02  thf(d2_subset_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( ( v1_xboole_0 @ A ) =>
% 0.81/1.02         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.81/1.02       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/1.02         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.81/1.02  thf('48', plain,
% 0.81/1.02      (![X5 : $i, X6 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ X6 @ X5) | (v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ X5))),
% 0.81/1.02      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.81/1.02  thf('49', plain,
% 0.81/1.02      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.81/1.02        | (v1_xboole_0 @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['47', '48'])).
% 0.81/1.02  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.81/1.02  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/1.02      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/1.02  thf('51', plain,
% 0.81/1.02      ((v1_xboole_0 @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('demod', [status(thm)], ['49', '50'])).
% 0.81/1.02  thf(l13_xboole_0, axiom,
% 0.81/1.02    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.81/1.02  thf('52', plain,
% 0.81/1.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.81/1.02  thf('53', plain,
% 0.81/1.02      (((sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['51', '52'])).
% 0.81/1.02  thf('54', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.81/1.02      inference('demod', [status(thm)], ['39', '53'])).
% 0.81/1.02  thf('55', plain,
% 0.81/1.02      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.81/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.81/1.02  thf(l3_subset_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.81/1.02  thf('56', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         (~ (r2_hidden @ X7 @ X8)
% 0.81/1.02          | (r2_hidden @ X7 @ X9)
% 0.81/1.02          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.81/1.02      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.81/1.02  thf('57', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['55', '56'])).
% 0.81/1.02  thf('58', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ X0)),
% 0.81/1.02      inference('sup-', [status(thm)], ['54', '57'])).
% 0.81/1.02  thf('59', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['44', '45'])).
% 0.81/1.02  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ X0)),
% 0.81/1.02      inference('sup-', [status(thm)], ['58', '59'])).
% 0.81/1.02  thf('61', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ X0)),
% 0.81/1.02      inference('sup-', [status(thm)], ['54', '57'])).
% 0.81/1.02  thf('62', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['42', '43'])).
% 0.81/1.02  thf('63', plain,
% 0.81/1.02      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.81/1.02          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.81/1.02          | ~ (r2_hidden @ X27 @ (k3_orders_2 @ X28 @ X29 @ X30))
% 0.81/1.02          | (r2_orders_2 @ X28 @ X27 @ X30)
% 0.81/1.02          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.81/1.02          | ~ (l1_orders_2 @ X28)
% 0.81/1.02          | ~ (v5_orders_2 @ X28)
% 0.81/1.02          | ~ (v4_orders_2 @ X28)
% 0.81/1.02          | ~ (v3_orders_2 @ X28)
% 0.81/1.02          | (v2_struct_0 @ X28))),
% 0.81/1.02      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.81/1.02  thf('64', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         ((v2_struct_0 @ X0)
% 0.81/1.02          | ~ (v3_orders_2 @ X0)
% 0.81/1.02          | ~ (v4_orders_2 @ X0)
% 0.81/1.02          | ~ (v5_orders_2 @ X0)
% 0.81/1.02          | ~ (l1_orders_2 @ X0)
% 0.81/1.02          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.81/1.02          | (r2_orders_2 @ X0 @ X2 @ X1)
% 0.81/1.02          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ (u1_struct_0 @ X0) @ X1))
% 0.81/1.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/1.02  thf('65', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ k1_xboole_0 @ (u1_struct_0 @ X1))
% 0.81/1.02          | (r2_orders_2 @ X1 @ k1_xboole_0 @ X0)
% 0.81/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.81/1.02          | ~ (l1_orders_2 @ X1)
% 0.81/1.02          | ~ (v5_orders_2 @ X1)
% 0.81/1.02          | ~ (v4_orders_2 @ X1)
% 0.81/1.02          | ~ (v3_orders_2 @ X1)
% 0.81/1.02          | (v2_struct_0 @ X1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['61', '64'])).
% 0.81/1.02  thf('66', plain, (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ X0)),
% 0.81/1.02      inference('sup-', [status(thm)], ['58', '59'])).
% 0.81/1.02  thf('67', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r2_orders_2 @ X1 @ k1_xboole_0 @ X0)
% 0.81/1.02          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.81/1.02          | ~ (l1_orders_2 @ X1)
% 0.81/1.02          | ~ (v5_orders_2 @ X1)
% 0.81/1.02          | ~ (v4_orders_2 @ X1)
% 0.81/1.02          | ~ (v3_orders_2 @ X1)
% 0.81/1.02          | (v2_struct_0 @ X1))),
% 0.81/1.02      inference('demod', [status(thm)], ['65', '66'])).
% 0.81/1.02  thf('68', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((v2_struct_0 @ X0)
% 0.81/1.02          | ~ (v3_orders_2 @ X0)
% 0.81/1.02          | ~ (v4_orders_2 @ X0)
% 0.81/1.02          | ~ (v5_orders_2 @ X0)
% 0.81/1.02          | ~ (l1_orders_2 @ X0)
% 0.81/1.02          | (r2_orders_2 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['60', '67'])).
% 0.81/1.02  thf('69', plain,
% 0.81/1.02      ((m1_subset_1 @ 
% 0.81/1.02        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02        (u1_struct_0 @ sk_A))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.81/1.02  thf(d10_orders_2, axiom,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( l1_orders_2 @ A ) =>
% 0.81/1.02       ( ![B:$i]:
% 0.81/1.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02           ( ![C:$i]:
% 0.81/1.02             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.81/1.02                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.81/1.02  thf('70', plain,
% 0.81/1.02      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.81/1.02          | ~ (r2_orders_2 @ X21 @ X20 @ X22)
% 0.81/1.02          | ((X20) != (X22))
% 0.81/1.02          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.81/1.02          | ~ (l1_orders_2 @ X21))),
% 0.81/1.02      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.81/1.02  thf('71', plain,
% 0.81/1.02      (![X21 : $i, X22 : $i]:
% 0.81/1.02         (~ (l1_orders_2 @ X21)
% 0.81/1.02          | ~ (r2_orders_2 @ X21 @ X22 @ X22)
% 0.81/1.02          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['70'])).
% 0.81/1.02  thf('72', plain,
% 0.81/1.02      ((~ (r2_orders_2 @ sk_A @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02            (u1_struct_0 @ sk_A)))
% 0.81/1.02        | ~ (l1_orders_2 @ sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['69', '71'])).
% 0.81/1.02  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('74', plain,
% 0.81/1.02      (~ (r2_orders_2 @ sk_A @ 
% 0.81/1.02          (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02           (u1_struct_0 @ sk_A)) @ 
% 0.81/1.02          (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02           (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('demod', [status(thm)], ['72', '73'])).
% 0.81/1.02  thf('75', plain,
% 0.81/1.02      (((sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['51', '52'])).
% 0.81/1.02  thf('76', plain,
% 0.81/1.02      (((sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.81/1.02         (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['51', '52'])).
% 0.81/1.02  thf('77', plain, (~ (r2_orders_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.81/1.02      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.81/1.02  thf('78', plain,
% 0.81/1.02      ((~ (l1_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v5_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v4_orders_2 @ sk_A)
% 0.81/1.02        | ~ (v3_orders_2 @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['68', '77'])).
% 0.81/1.02  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('80', plain, ((v5_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('81', plain, ((v4_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('83', plain, ((v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.81/1.02  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.81/1.02  
% 0.81/1.02  % SZS output end Refutation
% 0.81/1.02  
% 0.81/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
