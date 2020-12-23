%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PGunJQ4Rvo

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 136 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  522 (1586 expanded)
%              Number of equality atoms :   13 (  60 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
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

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('13',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('15',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
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

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k3_orders_2 @ X15 @ X16 @ X17 ) )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('28',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','19'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','30','31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['36','37'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PGunJQ4Rvo
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 78 iterations in 0.045s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.49  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.19/0.49  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(t60_orders_2, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.19/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t4_subset_1, axiom,
% 0.19/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.49  thf(dt_k3_orders_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.19/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49       ( m1_subset_1 @
% 0.19/0.49         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.49          | ~ (l1_orders_2 @ X11)
% 0.19/0.49          | ~ (v5_orders_2 @ X11)
% 0.19/0.49          | ~ (v4_orders_2 @ X11)
% 0.19/0.49          | ~ (v3_orders_2 @ X11)
% 0.19/0.49          | (v2_struct_0 @ X11)
% 0.19/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.19/0.49          | (m1_subset_1 @ (k3_orders_2 @ X11 @ X10 @ X12) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.19/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.49          | (v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v3_orders_2 @ X0)
% 0.19/0.49          | ~ (v4_orders_2 @ X0)
% 0.19/0.49          | ~ (v5_orders_2 @ X0)
% 0.19/0.49          | ~ (l1_orders_2 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((~ (l1_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v4_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v3_orders_2 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.49  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.19/0.49  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf(t10_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49            ( ![C:$i]:
% 0.19/0.49              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X1 : $i, X2 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.19/0.49          | ((X1) = (k1_xboole_0))
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.49        | (r2_hidden @ 
% 0.19/0.49           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49            (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49           (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf(d2_struct_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X9 : $i]:
% 0.19/0.49         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_l1_orders_2, axiom,
% 0.19/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_orders_2 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.19/0.49  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((r2_hidden @ 
% 0.19/0.49        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49         (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49        (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['13', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.49  thf(t57_orders_2, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.19/0.49                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.19/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.49          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 0.19/0.49          | (r2_hidden @ X14 @ X16)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.19/0.49          | ~ (l1_orders_2 @ X15)
% 0.19/0.49          | ~ (v5_orders_2 @ X15)
% 0.19/0.49          | ~ (v4_orders_2 @ X15)
% 0.19/0.49          | ~ (v3_orders_2 @ X15)
% 0.19/0.49          | (v2_struct_0 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v3_orders_2 @ X0)
% 0.19/0.49          | ~ (v4_orders_2 @ X0)
% 0.19/0.49          | ~ (v5_orders_2 @ X0)
% 0.19/0.49          | ~ (l1_orders_2 @ X0)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.49          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.19/0.49          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.19/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((~ (m1_subset_1 @ 
% 0.19/0.49           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49            (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49           (u1_struct_0 @ sk_A))
% 0.19/0.49        | (r2_hidden @ 
% 0.19/0.49           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49            (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49           k1_xboole_0)
% 0.19/0.49        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | ~ (l1_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v4_orders_2 @ sk_A)
% 0.19/0.49        | ~ (v3_orders_2 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X1 : $i, X2 : $i]:
% 0.19/0.49         ((m1_subset_1 @ (sk_C @ X1 @ X2) @ X2)
% 0.19/0.49          | ((X1) = (k1_xboole_0))
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ 
% 0.19/0.49           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49            (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49           (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((m1_subset_1 @ 
% 0.19/0.49        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49         (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49        (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('34', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (((r2_hidden @ 
% 0.19/0.49         (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49          (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49         k1_xboole_0)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)],
% 0.19/0.49                ['25', '30', '31', '32', '33', '34', '35'])).
% 0.19/0.49  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((r2_hidden @ 
% 0.19/0.49        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49         (u1_struct_0 @ sk_A)) @ 
% 0.19/0.49        k1_xboole_0)),
% 0.19/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf(t7_ordinal1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.19/0.49          (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.19/0.49           (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.49  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('42', plain, ($false), inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
