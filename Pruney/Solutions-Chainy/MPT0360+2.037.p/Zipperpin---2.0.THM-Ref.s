%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GalWID2gSw

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 131 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   20
%              Number of atoms          :  425 (1003 expanded)
%              Number of equality atoms :   13 (  32 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X14 @ ( k3_subset_1 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ X16 @ ( k3_subset_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
      | ( r1_tarski @ sk_C_2 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X18 ) )
      | ( X18
        = ( k1_subset_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k1_subset_1 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X18 ) )
      | ( X18 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('44',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GalWID2gSw
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:03:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 124 iterations in 0.069s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf(t40_subset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.51         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51          ( ( ( r1_tarski @ B @ C ) & 
% 0.20/0.51              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.51            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.20/0.51  thf('1', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf('5', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t35_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.20/0.51             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.20/0.51          | (r1_tarski @ X14 @ (k3_subset_1 @ X15 @ X16))
% 0.20/0.51          | ~ (r1_tarski @ X16 @ (k3_subset_1 @ X15 @ X14))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 0.20/0.51          | (r1_tarski @ sk_C_2 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((r1_tarski @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf('11', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d2_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X9 @ X10)
% 0.20/0.51          | (r2_hidden @ X9 @ X10)
% 0.20/0.51          | (v1_xboole_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(fc1_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('14', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('15', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf(d1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X7 @ X6)
% 0.20/0.51          | (r1_tarski @ X7 @ X5)
% 0.20/0.51          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X5 : $i, X7 : $i]:
% 0.20/0.51         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('23', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X4 @ X5)
% 0.20/0.51          | (r2_hidden @ X4 @ X6)
% 0.20/0.51          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((r2_hidden @ X4 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.51  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.51          | (m1_subset_1 @ X9 @ X10)
% 0.20/0.51          | (v1_xboole_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, ((r1_tarski @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.51        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.51  thf(t38_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.51         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X18))
% 0.20/0.51          | ((X18) = (k1_subset_1 @ X17))
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.20/0.51  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('40', plain, (![X12 : $i]: ((k1_subset_1 @ X12) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X18))
% 0.20/0.52          | ((X18) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.52  thf('43', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('44', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
