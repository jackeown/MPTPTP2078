%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a3SCCwafT1

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 114 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  359 ( 867 expanded)
%              Number of equality atoms :   13 (  36 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ X16 @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('30',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
      | ( X20
        = ( k1_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('36',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a3SCCwafT1
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:05:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 272 iterations in 0.171s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(t40_subset_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.39/0.61         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.61        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61          ( ( ( r1_tarski @ B @ C ) & 
% 0.39/0.61              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.39/0.61            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.39/0.61  thf('0', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t35_subset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61       ( ![C:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.39/0.61             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.39/0.61          | (r1_tarski @ X16 @ (k3_subset_1 @ X17 @ X18))
% 0.39/0.61          | ~ (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.39/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.61          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.39/0.61          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.39/0.61        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.61  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d2_subset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X12 @ X13)
% 0.39/0.61          | (r2_hidden @ X12 @ X13)
% 0.39/0.61          | (v1_xboole_0 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.61        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.61  thf(d1_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.39/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X10 @ X9)
% 0.39/0.61          | (r1_tarski @ X10 @ X8)
% 0.39/0.61          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X8 : $i, X10 : $i]:
% 0.39/0.61         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['7', '9'])).
% 0.39/0.61  thf('11', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t1_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.61       ( r1_tarski @ A @ C ) ))).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.61         (~ (r1_tarski @ X3 @ X4)
% 0.39/0.61          | ~ (r1_tarski @ X4 @ X5)
% 0.39/0.61          | (r1_tarski @ X3 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['10', '13'])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.61         (~ (r1_tarski @ X7 @ X8)
% 0.39/0.61          | (r2_hidden @ X7 @ X9)
% 0.39/0.61          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((r2_hidden @ X7 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X7 @ X8))),
% 0.39/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.61        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['14', '16'])).
% 0.39/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.61  thf('18', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.39/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((r2_hidden @ X7 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X7 @ X8))),
% 0.39/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.61  thf(d1_xboole_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.61  thf('22', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.61  thf('23', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['17', '22'])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X12 @ X13)
% 0.39/0.61          | (m1_subset_1 @ X12 @ X13)
% 0.39/0.61          | (v1_xboole_0 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i]:
% 0.39/0.61         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.39/0.61      inference('clc', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '26'])).
% 0.39/0.61  thf('28', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['4', '27'])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.61  thf('30', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf(t38_subset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.39/0.61         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X19 : $i, X20 : $i]:
% 0.39/0.61         (~ (r1_tarski @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.39/0.61          | ((X20) = (k1_subset_1 @ X19))
% 0.39/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.39/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('32', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X19 : $i, X20 : $i]:
% 0.39/0.61         (~ (r1_tarski @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.39/0.61          | ((X20) = (k1_xboole_0))
% 0.39/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.39/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.61        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['30', '33'])).
% 0.39/0.61  thf('35', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '26'])).
% 0.39/0.61  thf('36', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.61  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('38', plain, ($false),
% 0.39/0.61      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
