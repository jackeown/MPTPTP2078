%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P7MipYD1Js

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  455 (1211 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('6',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_tarski @ X9 @ X7 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['14','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P7MipYD1Js
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 81 iterations in 0.030s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(t44_subset_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.22/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49          ( ![C:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.22/0.49                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.49        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.22/0.49       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.49        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf(t85_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.49          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d5_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.22/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.22/0.49         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.22/0.49         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.22/0.49       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.22/0.49  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.22/0.49  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.22/0.49  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d2_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X11 @ X12)
% 0.22/0.49          | (r2_hidden @ X11 @ X12)
% 0.22/0.49          | (v1_xboole_0 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf(fc1_subset_1, axiom,
% 0.22/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.49  thf('18', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.49  thf('19', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf(d1_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X9 @ X8)
% 0.22/0.49          | (r1_tarski @ X9 @ X7)
% 0.22/0.49          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X7 : $i, X9 : $i]:
% 0.22/0.49         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.49  thf('22', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.22/0.49         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf(t86_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.49       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.50          | ~ (r1_xboole_0 @ X3 @ X5)
% 0.22/0.50          | (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((r1_tarski @ sk_B @ 
% 0.22/0.50            (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.22/0.50           | ~ (r1_tarski @ sk_B @ X0)))
% 0.22/0.50         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((r1_tarski @ sk_B @ 
% 0.22/0.50            (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.22/0.50           | ~ (r1_tarski @ sk_B @ X0)))
% 0.22/0.50         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.22/0.50       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('29', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['2', '12', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_B @ 
% 0.22/0.50           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.22/0.50          | ~ (r1_tarski @ sk_B @ X0))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '30'])).
% 0.22/0.50  thf('32', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.22/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.22/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k3_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.22/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.22/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.22/0.50         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (((sk_C_1) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['36', '43'])).
% 0.22/0.50  thf('45', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['31', '44'])).
% 0.22/0.50  thf('46', plain, ($false), inference('demod', [status(thm)], ['14', '45'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
