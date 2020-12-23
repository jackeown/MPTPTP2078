%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tWCP9GtGKw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  571 (1273 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
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
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('22',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
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

thf('28',plain,(
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

thf('29',plain,(
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
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33','34','35','36'])).

thf('38',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('43',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tWCP9GtGKw
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 171 iterations in 0.156s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.60  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.21/0.60  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.60  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.60  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.60  thf(t7_xboole_0, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.60  thf('0', plain,
% 0.21/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf(t60_orders_2, conjecture,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.60           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i]:
% 0.21/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.60            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.60          ( ![B:$i]:
% 0.21/0.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.60              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.21/0.60  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t4_subset_1, axiom,
% 0.21/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.60  thf(dt_k3_orders_2, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60       ( m1_subset_1 @
% 0.21/0.60         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.60          | ~ (l1_orders_2 @ X11)
% 0.21/0.60          | ~ (v5_orders_2 @ X11)
% 0.21/0.60          | ~ (v4_orders_2 @ X11)
% 0.21/0.60          | ~ (v3_orders_2 @ X11)
% 0.21/0.60          | (v2_struct_0 @ X11)
% 0.21/0.60          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.60          | (m1_subset_1 @ (k3_orders_2 @ X11 @ X10 @ X12) @ 
% 0.21/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.21/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.60          | (v2_struct_0 @ X0)
% 0.21/0.60          | ~ (v3_orders_2 @ X0)
% 0.21/0.60          | ~ (v4_orders_2 @ X0)
% 0.21/0.60          | ~ (v5_orders_2 @ X0)
% 0.21/0.60          | ~ (l1_orders_2 @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.60        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.60        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.60        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.21/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.60  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.21/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.60      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.21/0.60  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.21/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.60  thf(t4_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.60          | (m1_subset_1 @ X3 @ X5))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.60          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 0.21/0.60        | (m1_subset_1 @ 
% 0.21/0.60           (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.21/0.60           (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '14'])).
% 0.21/0.60  thf(fc3_struct_0, axiom,
% 0.21/0.60    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X9 : $i]: ((v1_xboole_0 @ (k1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.21/0.60      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.21/0.60  thf(t6_boole, axiom,
% 0.21/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.60      inference('cnf', [status(esa)], [t6_boole])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (l1_struct_0 @ X0) | ((k1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))
% 0.21/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.60  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(dt_l1_orders_2, axiom,
% 0.21/0.60    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_orders_2 @ X13))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.60  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.21/0.60        (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['15', '24'])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.60  thf(t57_orders_2, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.60               ( ![D:$i]:
% 0.21/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.21/0.60                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('28', plain,
% 0.21/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.21/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.60          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 0.21/0.60          | (r2_hidden @ X14 @ X16)
% 0.21/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.21/0.60          | ~ (l1_orders_2 @ X15)
% 0.21/0.60          | ~ (v5_orders_2 @ X15)
% 0.21/0.60          | ~ (v4_orders_2 @ X15)
% 0.21/0.60          | ~ (v3_orders_2 @ X15)
% 0.21/0.60          | (v2_struct_0 @ X15))),
% 0.21/0.60      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((v2_struct_0 @ X0)
% 0.21/0.60          | ~ (v3_orders_2 @ X0)
% 0.21/0.60          | ~ (v4_orders_2 @ X0)
% 0.21/0.60          | ~ (v5_orders_2 @ X0)
% 0.21/0.60          | ~ (l1_orders_2 @ X0)
% 0.21/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.60          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.21/0.60          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.21/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (((k3_orders_2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.60          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.60               (u1_struct_0 @ X1))
% 0.21/0.60          | (r2_hidden @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.60             k1_xboole_0)
% 0.21/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.60          | ~ (l1_orders_2 @ X1)
% 0.21/0.60          | ~ (v5_orders_2 @ X1)
% 0.21/0.60          | ~ (v4_orders_2 @ X1)
% 0.21/0.60          | ~ (v3_orders_2 @ X1)
% 0.21/0.60          | (v2_struct_0 @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.60        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.60        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.60        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.60        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.60        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.21/0.60           k1_xboole_0)
% 0.21/0.60        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.60  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('36', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.21/0.60           k1_xboole_0)
% 0.21/0.60        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['31', '32', '33', '34', '35', '36'])).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.21/0.60           k1_xboole_0))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.21/0.60        k1_xboole_0)),
% 0.21/0.60      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.60      inference('cnf', [status(esa)], [t6_boole])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.60      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.60  thf(t5_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.60          | ~ (v1_xboole_0 @ X8)
% 0.21/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.60  thf('46', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.60      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.60  thf('48', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['41', '47'])).
% 0.21/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.60  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.60  thf('50', plain, ($false), inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.45/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
